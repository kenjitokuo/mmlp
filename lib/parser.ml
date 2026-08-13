type token =
  | Ident of string
  | Integer of int
  | LParen
  | RParen
  | LBracket
  | RBracket
  | Comma
  | Dot
  | Not
  | And
  | Or
  | Imp
  | End

exception Parse_error of string

let is_space = function
  | ' ' | '\t' | '\r' | '\n' -> true
  | _ -> false

let is_digit c =
  c >= '0' && c <= '9'

let is_letter c =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || c = '_'

let is_identifier_character c =
  is_letter c || is_digit c || c = '\''

let tokenize input =
  let length = String.length input in

  let rec skip_spaces i =
    if i < length && is_space input.[i] then
      skip_spaces (i + 1)
    else
      i
  in

  let rec identifier_end i =
    if
      i < length
      && is_identifier_character input.[i]
    then
      identifier_end (i + 1)
    else
      i
  in

  let rec integer_end i =
    if i < length && is_digit input.[i] then
      integer_end (i + 1)
    else
      i
  in

  let rec loop i tokens =
    let i = skip_spaces i in
    if i >= length then
      List.rev (End :: tokens)
    else
      match input.[i] with
      | '(' ->
          loop (i + 1) (LParen :: tokens)

      | ')' ->
          loop (i + 1) (RParen :: tokens)

      | '[' ->
          loop (i + 1) (LBracket :: tokens)

      | ']' ->
          loop (i + 1) (RBracket :: tokens)

      | ',' ->
          loop (i + 1) (Comma :: tokens)

      | '.' ->
          loop (i + 1) (Dot :: tokens)

      | '~'
      | '!' ->
          loop (i + 1) (Not :: tokens)

      | '&' ->
          loop (i + 1) (And :: tokens)

      | '|' ->
          loop (i + 1) (Or :: tokens)

      | '-' ->
          if
            i + 1 < length
            && input.[i + 1] = '>'
          then
            loop (i + 2) (Imp :: tokens)
          else
            raise
              (Parse_error
                 ("expected '>' after '-' at position "
                  ^ string_of_int i))

      | c when is_digit c ->
          let stop = integer_end (i + 1) in
          let text =
            String.sub input i (stop - i)
          in
          loop
            stop
            (Integer (int_of_string text) :: tokens)

      | c when is_letter c ->
          let stop = identifier_end (i + 1) in
          let text =
            String.sub input i (stop - i)
          in
          let token =
            match String.lowercase_ascii text with
            | "not" -> Not
            | "and" -> And
            | "or" -> Or
            | _ -> Ident text
          in
          loop stop (token :: tokens)

      | c ->
          raise
            (Parse_error
               ("unexpected character '"
                ^ String.make 1 c
                ^ "' at position "
                ^ string_of_int i))
  in

  loop 0 []

type stream = {
  tokens : token array;
  mutable position : int;
}

let make_stream tokens =
  {
    tokens = Array.of_list tokens;
    position = 0;
  }

let peek stream =
  if stream.position < Array.length stream.tokens then
    stream.tokens.(stream.position)
  else
    End

let consume stream =
  let token = peek stream in
  stream.position <- stream.position + 1;
  token

let expect stream expected =
  match consume stream with
  | token when token = expected ->
      ()
  | _ ->
      raise (Parse_error "unexpected token")

let is_free_variable_name name =
  String.length name > 0
  &&
  let c = name.[0] in
  (c >= 'A' && c <= 'Z') || c = '_'

let is_variable bound_variables name =
  is_free_variable_name name
  || List.mem name bound_variables

let rec parse_term_stream bound_variables stream =
  match consume stream with
  | Ident name ->
      begin
        match peek stream with
        | LParen ->
            if is_variable bound_variables name then
              raise
                (Parse_error
                   "a variable cannot be used as a function symbol");
            ignore (consume stream);
            Syntax.Fun
              ( name,
                parse_term_arguments
                  bound_variables
                  stream )

        | _ ->
            if is_variable bound_variables name then
              Syntax.Var name
            else
              Syntax.Const name
      end

  | _ ->
      raise (Parse_error "expected a term")

and parse_term_arguments bound_variables stream =
  match peek stream with
  | RParen ->
      ignore (consume stream);
      []

  | _ ->
      let first =
        parse_term_stream bound_variables stream
      in
      let rec loop arguments =
        match peek stream with
        | Comma ->
            ignore (consume stream);
            let argument =
              parse_term_stream
                bound_variables
                stream
            in
            loop (argument :: arguments)

        | RParen ->
            ignore (consume stream);
            List.rev arguments

        | _ ->
            raise
              (Parse_error
                 "expected ',' or ')' in term argument list")
      in
      loop [first]

let modal_index ~max_modal_index index =
  match
    Syntax.make_modal_index
      ~max_index:max_modal_index
      index
  with
  | Ok modality ->
      modality
  | Error message ->
      raise (Parse_error message)

let rec parse_formula_stream
    ~max_modal_index
    ~bound_variables
    stream =
  parse_implication
    ~max_modal_index
    ~bound_variables
    stream

and parse_implication
    ~max_modal_index
    ~bound_variables
    stream =
  let left =
    parse_disjunction
      ~max_modal_index
      ~bound_variables
      stream
  in
  match peek stream with
  | Imp ->
      ignore (consume stream);
      let right =
        parse_implication
          ~max_modal_index
          ~bound_variables
          stream
      in
      Syntax.Imp (left, right)

  | _ ->
      left

and parse_disjunction
    ~max_modal_index
    ~bound_variables
    stream =
  let first =
    parse_conjunction
      ~max_modal_index
      ~bound_variables
      stream
  in
  let rec loop left =
    match peek stream with
    | Or ->
        ignore (consume stream);
        let right =
          parse_conjunction
            ~max_modal_index
            ~bound_variables
            stream
        in
        loop (Syntax.Or (left, right))

    | _ ->
        left
  in
  loop first

and parse_conjunction
    ~max_modal_index
    ~bound_variables
    stream =
  let first =
    parse_unary
      ~max_modal_index
      ~bound_variables
      stream
  in
  let rec loop left =
    match peek stream with
    | And ->
        ignore (consume stream);
        let right =
          parse_unary
            ~max_modal_index
            ~bound_variables
            stream
        in
        loop (Syntax.And (left, right))

    | _ ->
        left
  in
  loop first

and parse_unary
    ~max_modal_index
    ~bound_variables
    stream =
  match peek stream with
  | Not ->
      ignore (consume stream);
      Syntax.Not
        (parse_unary
           ~max_modal_index
           ~bound_variables
           stream)

  | Ident keyword
    when
      String.equal
        (String.lowercase_ascii keyword)
        "forall" ->
      ignore (consume stream);
      let variable =
        match consume stream with
        | Ident name ->
            name
        | _ ->
            raise
              (Parse_error
                 "expected variable after 'forall'")
      in
      expect stream Dot;
      Syntax.Forall
        ( variable,
          parse_formula_stream
            ~max_modal_index
            ~bound_variables:
              (variable :: bound_variables)
            stream )

  | Ident keyword
    when
      String.equal
        (String.lowercase_ascii keyword)
        "exists" ->
      ignore (consume stream);
      let variable =
        match consume stream with
        | Ident name ->
            name
        | _ ->
            raise
              (Parse_error
                 "expected variable after 'exists'")
      in
      expect stream Dot;
      Syntax.Exists
        ( variable,
          parse_formula_stream
            ~max_modal_index
            ~bound_variables:
              (variable :: bound_variables)
            stream )

  | Ident keyword
    when
      String.equal
        (String.lowercase_ascii keyword)
        "box" ->
      ignore (consume stream);
      expect stream LBracket;
      let index =
        match consume stream with
        | Integer index ->
            index
        | _ ->
            raise
              (Parse_error
                 "expected modal index in box[...]")
      in
      expect stream RBracket;
      Syntax.Box
        ( modal_index ~max_modal_index index,
          parse_unary
            ~max_modal_index
            ~bound_variables
            stream )

  | Ident keyword
    when
      String.equal
        (String.lowercase_ascii keyword)
        "diamond" ->
      ignore (consume stream);
      expect stream LBracket;
      let index =
        match consume stream with
        | Integer index ->
            index
        | _ ->
            raise
              (Parse_error
                 "expected modal index in diamond[...]")
      in
      expect stream RBracket;
      Syntax.Diamond
        ( modal_index ~max_modal_index index,
          parse_unary
            ~max_modal_index
            ~bound_variables
            stream )

  | LParen ->
      ignore (consume stream);
      let formula =
        parse_formula_stream
          ~max_modal_index
          ~bound_variables
          stream
      in
      expect stream RParen;
      formula

  | Ident name ->
      ignore (consume stream);
      begin
        match String.lowercase_ascii name with
        | "bottom"
        | "false" ->
            Syntax.Bottom

        | "top"
        | "true" ->
            Syntax.Not Syntax.Bottom

        | _ ->
            begin
              match peek stream with
              | LParen ->
                  ignore (consume stream);
                  let arguments =
                    parse_term_arguments
                      bound_variables
                      stream
                  in
                  Syntax.Atom (name, arguments)

              | _ ->
                  Syntax.Atom (name, [])
            end
      end

  | _ ->
      raise (Parse_error "expected a formula")

let finish stream =
  match peek stream with
  | End ->
      ()
  | _ ->
      raise
        (Parse_error
           "unexpected input after complete expression")

let parse_term input =
  try
    let stream =
      make_stream (tokenize input)
    in
    let term =
      parse_term_stream [] stream
    in
    finish stream;
    Ok term
  with
  | Parse_error message ->
      Error message
  | Failure message ->
      Error message

let parse_formula
    ~max_modal_index
    input =
  try
    let stream =
      make_stream (tokenize input)
    in
    let formula =
      parse_formula_stream
        ~max_modal_index
        ~bound_variables:[]
        stream
    in
    finish stream;
    Ok formula
  with
  | Parse_error message ->
      Error message
  | Failure message ->
      Error message
