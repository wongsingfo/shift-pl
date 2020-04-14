let file_name = ref ""
let usage = Printf.sprintf "usage: %s [file-name]" Sys.argv.(0)

let () =
  Arg.parse [] (fun f -> file_name := f) usage;
  let lexbuf =
    Lexing.from_channel @@ if !file_name = "" then stdin else open_in !file_name
  in
  try
    while true do
      let term = Parser.top_level Lexer.main lexbuf in
      print_string (Syntax.term2string term);
      print_newline ();
      flush stdout
    done
  with
  | Lexer.Eof -> exit 0
;;
