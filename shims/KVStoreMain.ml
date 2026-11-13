open Datatypes

open Util
open Debug
open Shim

(* NB: [String] here is the module extracted from Coq's String library
   (Coq strings are lists of 8-bit ascii values), not OCaml's Stdlib.String. *)

type mode = Primary | Backup | Client

let mode : mode option ref = ref None
let me : Datatypes.nat option ref = ref None
let linger : int ref = ref 3
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
  print_endline "    -mode <MODE>      primary, backup or client (required)";
  print_endline "    -linger <SECS>    how long a client keeps its connections open";
  print_endline "                      after it is done (default 3)";
  exit 1

let rec parse_args = function
  | [] -> ()
  | "-mode" :: "primary" :: args -> mode := Some Primary; parse_args args
  | "-mode" :: "backup" :: args -> mode := Some Backup; parse_args args
  | "-mode" :: "client" :: args -> mode := Some Client; parse_args args
  | "-me" :: name :: args -> me := Some (nat_of_string name); parse_args args
  | "-linger" :: n :: args -> linger := int_of_string n; parse_args args
  | name :: ip :: port :: args ->
     nodes := (nat_of_string name, (ip, int_of_string port)) :: !nodes;
     parse_args args
  | arg :: _ -> usage ("Unknown argument " ^ arg)

(* Printing VarD inputs and outputs *)

let char_of_ascii (Ascii.Ascii (b0, b1, b2, b3, b4, b5, b6, b7)) =
  let bit b n = if b then 1 lsl n else 0 in
  Char.chr (bit b0 0 + bit b1 1 + bit b2 2 + bit b3 3 +
            bit b4 4 + bit b5 5 + bit b6 6 + bit b7 7)

let ocaml_string (s : String.string) : string =
  let buf = Buffer.create 16 in
  let rec go = function
    | String.EmptyString -> ()
    | String.String (a, s') -> Buffer.add_char buf (char_of_ascii a); go s'
  in
  go s; Buffer.contents buf

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

let main () =
  parse_args (List.tl (Array.to_list Sys.argv));
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
     | _, n -> usage (Printf.sprintf "node %d cannot run in this mode" n)
    end
  | _, _ -> usage "-mode and -me must be given"

let _ = main ()
