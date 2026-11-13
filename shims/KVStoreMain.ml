open Datatypes

open Util
open Debug
open Shim

(* NB: [String] here is the module extracted from Coq's String library
   (Coq strings are lists of 8-bit ascii values), not OCaml's Stdlib.String. *)

type mode = Primary | Backup | Client | Repl

let mode : mode option ref = ref None
let me : Datatypes.nat option ref = ref None
let linger : int ref = ref 3
let verbose : int option ref = ref None
let nodes : (Datatypes.nat * (string * int)) list ref = ref []

let usage msg =
  print_endline msg;
  Printf.printf "%s usage:\n" Sys.argv.(0);
  Printf.printf "    %s [OPTIONS] <CLUSTER>\n" (Array.get Sys.argv 0);
  print_endline "where:";
  print_endline "    CLUSTER   is a list of triples of ID IP_ADDR PORT,";
  print_endline "              giving all the nodes in the system";
  print_newline ();
  print_endline "Options are as follows:";
  print_endline "    -me <NAME>        the identity of this node (required)";
  print_endline "    -mode <MODE>      primary (node 1), backup (node 2), or, for";
  print_endline "                      nodes 3 and 4: client (run a fixed list of";
  print_endline "                      requests) or repl (read requests from stdin)";
  print_endline "    -v <0|1|2>        shim output: 0 none, 1 messages, 2 also states";
  print_endline "                      (default 2, but 0 in repl mode)";
  print_endline "    -linger <SECS>    how long a client keeps its connections open";
  print_endline "                      after it is done (default 3)";
  exit 1

let rec parse_args = function
  | [] -> ()
  | "-mode" :: "primary" :: args -> mode := Some Primary; parse_args args
  | "-mode" :: "backup" :: args -> mode := Some Backup; parse_args args
  | "-mode" :: "client" :: args -> mode := Some Client; parse_args args
  | "-mode" :: "repl" :: args -> mode := Some Repl; parse_args args
  | "-me" :: name :: args -> me := Some (nat_of_string name); parse_args args
  | "-v" :: n :: args -> verbose := Some (int_of_string n); parse_args args
  | "-linger" :: n :: args -> linger := int_of_string n; parse_args args
  | name :: ip :: port :: args ->
     nodes := (nat_of_string name, (ip, int_of_string port)) :: !nodes;
     parse_args args
  | arg :: _ -> usage ("Unknown argument " ^ arg)

(* Converting between OCaml and Coq strings *)

let char_of_ascii (Ascii.Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let bit b n = if b then 1 lsl n else 0 in
  Char.chr (bit b0 0 + bit b1 1 + bit b2 2 + bit b3 3 +
            bit b4 4 + bit b5 5 + bit b6 6 + bit b7 7)

let ascii_of_char c =
  let n = Char.code c in
  let bit i = (n lsr i) land 1 = 1 in
  Ascii.Ascii (bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7)

let ocaml_string (s : String.string) : string =
  let buf = Buffer.create 16 in
  let rec go = function
    | String.EmptyString -> ()
    | String.String (a, s') -> Buffer.add_char buf (char_of_ascii a); go s'
  in
  go s; Buffer.contents buf

let coq_string (s : string) : String.string =
  let rec go i =
    if i >= Stdlib.String.length s then String.EmptyString
    else String.String (ascii_of_char (Stdlib.String.get s i), go (i + 1))
  in
  go 0

(* Printing VarD inputs and outputs *)

let show_str s = Printf.sprintf "%S" (ocaml_string s)

let show_opt = function
  | None -> "None"
  | Some v -> "Some " ^ show_str v

let show_input = function
  | VarD.Put (k, v) -> Printf.sprintf "Put %s %s" (show_str k) (show_str v)
  | VarD.Get k -> Printf.sprintf "Get %s" (show_str k)
  | VarD.Del k -> Printf.sprintf "Del %s" (show_str k)
  | VarD.CAS (k, ov, v) ->
     Printf.sprintf "CAS %s (%s) %s" (show_str k) (show_opt ov) (show_str v)
  | VarD.CAD (k, v) -> Printf.sprintf "CAD %s %s" (show_str k) (show_str v)

let show_output (VarD.Response (k, v, old)) =
  Printf.sprintf "Response %s (%s) (%s)" (show_str k) (show_opt v) (show_opt old)

let print_results l =
  List.iter (fun (i, o) ->
      Printf.printf "  %-28s => %s\n" (show_input i) (show_output o)) l;
  flush stdout

(* Interactive client. Command syntax matches experiments/vardpb:
     GET k | PUT k v | DEL k | CAS k old|- new | CAD k old
   Responses are printed as "Response KEY VALUE OLD", with "-" for None. *)

let repl_help () =
  print_endline "commands (keys and values are single words):";
  print_endline "  GET k            read k";
  print_endline "  PUT k v          set k to v";
  print_endline "  DEL k            delete k";
  print_endline "  CAS k old new    set k to new if it is currently old";
  print_endline "  CAS k - new      set k to new if it is currently unset";
  print_endline "  CAD k old        delete k if it is currently old";
  print_endline "  help | quit";
  flush stdout

type command = Input of VarD.input | Help | Quit | Skip | Bad

let parse_command line : command =
  let words =
    List.filter (fun w -> w <> "")
      (Stdlib.String.split_on_char ' '
         (Stdlib.String.map (function '\t' | '\r' -> ' ' | c -> c) line)) in
  let cs = coq_string in
  match words with
  | [] -> Skip
  | cmd :: args ->
     match Stdlib.String.uppercase_ascii cmd, args with
     | "GET", [k] -> Input (VarD.Get (cs k))
     | "PUT", [k; v] -> Input (VarD.Put (cs k, cs v))
     | "DEL", [k] -> Input (VarD.Del (cs k))
     | "CAS", [k; "-"; v] -> Input (VarD.CAS (cs k, None, cs v))
     | "CAS", [k; o; v] -> Input (VarD.CAS (cs k, Some (cs o), cs v))
     | "CAD", [k; o] -> Input (VarD.CAD (cs k, cs o))
     | ("HELP" | "?"), _ -> Help
     | ("QUIT" | "EXIT"), _ -> Quit
     | _ -> Bad

let show_opt_plain = function None -> "-" | Some v -> ocaml_string v

(* The [next] callback of the verified session loop (KVNodes.session):
   print the previous response, then read commands until we get a request
   (Some) or the user is done (None). *)
let repl_next (interactive : bool) (last_sent : float ref) prev =
  (match prev with
   | None -> ()
   | Some (_, VarD.Response (k, v, old)) ->
      let ms = (Unix.gettimeofday () -. !last_sent) *. 1000. in
      Printf.printf "Response %s %s %s%s\n%!" (ocaml_string k)
        (show_opt_plain v) (show_opt_plain old)
        (if interactive then Printf.sprintf "   (%.1f ms)" ms else ""));
  let rec read () =
    if interactive then (print_string "kv> "; flush stdout);
    match input_line stdin with
    | exception End_of_file -> if interactive then print_newline (); None
    | line ->
       match parse_command line with
       | Input i -> last_sent := Unix.gettimeofday (); Some i
       | Skip -> read ()
       | Help -> repl_help (); read ()
       | Quit -> None
       | Bad ->
          Printf.printf "bad command: %s  (type help)\n%!" (Stdlib.String.trim line);
          read ()
  in
  read ()

let main () =
  parse_args (List.tl (Array.to_list Sys.argv));
  (* Peers may come and go (e.g. clients started and stopped by hand), so
     never die because of a closed or unreachable connection. *)
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  Shim.drop_dead_connections := true;
  Shim.verbosity :=
    (match !verbose, !mode with
     | Some v, _ -> v
     | None, Some Repl -> 0
     | None, _ -> 2);
  match !mode, !me with
  | Some mode, Some me -> begin
     Shim.setup { nodes = !nodes; me = me; st = SimpleKVStoreApp.init_state };
     match mode, int_of_nat me with
     | Primary, 1 -> SimpleKVStoreApp.p_runner ()
     | Backup, 2 -> SimpleKVStoreApp.b_runner ()
     | Client, n when n = 3 || n = 4 ->
        let start = Unix.gettimeofday () in
        let l = if n = 3 then SimpleKVStoreApp.c_runner1 ()
                else SimpleKVStoreApp.c_runner2 () in
        let elapsed = Unix.gettimeofday () -. start in
        Printf.printf "client %d got %d responses in %.3fs:\n" n (List.length l) elapsed;
        print_results l;
        (* Keep our connections open for a while so that the primary's
           shim does not trip over a closed socket while other clients
           are still being served. *)
        Unix.sleep !linger
     | Repl, n when n = 3 || n = 4 ->
        let interactive = Unix.isatty Unix.stdin in
        if interactive then
          Printf.printf "Disel KV store, client node %d. Type help for commands.\n%!" n;
        let next = repl_next interactive (ref 0.) in
        ignore (if n = 3 then SimpleKVStoreApp.c_session1 next ()
                else SimpleKVStoreApp.c_session2 next ())
     | _, n -> usage (Printf.sprintf "node %d cannot run in this mode" n)
    end
  | _, _ -> usage "-mode and -me must be given"

let _ = main ()
