open Unix
open Printf
open Ast

(* Execute solver and read back output in string *)
let read_process command =
  let buffer_size = 2048 in
  let buffer = Buffer.create buffer_size in
  let string = Bytes.create buffer_size in
  let in_channel = Unix.open_process_in command in
  let chars_read = ref 1 in
  while !chars_read <> 0 do
    chars_read := input in_channel string 0 buffer_size;
    Buffer.add_substring buffer string 0 !chars_read
  done;
  ignore (Unix.close_process_in in_channel);
  Buffer.contents buffer

let parse_model inp model : modesat =
 let xlist = Str.split (Str.regexp " ") inp in
 let rec loop xs model = 
  match xs with
  | [] -> model
  | x::tail -> if (String.compare x "\n") = 0 then model else
		let xsign, pos, len' =
		let len = String.length x in
		let iszero = (Char.compare x.[0] '-') in
		if iszero = 0 then (0,1, len-1) else (1,0, len) in
		let xstr = String.sub x pos len' in
		let model' = ModeSAT.add (ModeVar xstr) xsign model
		in loop tail model'
 in loop xlist model

let extractsatmodel inp : modesat =
  let pos = Str.search_forward (Str.regexp "OPTIMUM FOUND") inp 0 in
  let _ = Printf.printf "Position: %d\n" pos in
  let start = Str.search_forward (Str.regexp "v ") inp pos in
  
  let _ = Printf.printf "V Position: %d\n" start in
  let posend = Str.search_forward (Str.regexp "c ") inp start in
  let _ = Printf.printf "C Position: %d\n" posend in

  let extractsat = String.sub inp (start + 2) (posend - start -2) in
  let _ = Printf.printf "%s\n" extractsat  in
  parse_model extractsat ModeSAT.empty


