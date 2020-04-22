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
      let term, ty = Infer.infer term in
      print_string
        (Syntax.term2string_with_annot term ^ " : " ^ Syntax.type2string_with_annot ty);
      print_newline ();
      flush stdout;

      print_string " ==>";

      let term_after_cps = Cps.cps term in
      print_string @@
        Syntax.term2string_with_annot term_after_cps;
      flush stdout;

      print_string "------------------------\n"
    done
  with
  | Lexer.Eof -> exit 0
;;
