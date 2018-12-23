type team = Korea | France | Usa | Brazil | Japan | Nigeria | Cameroon
          | Poland | Portugal | Italy | Germany | Norway | Sweden | England
          | Argentina
type tourna = LEAF of team
            | NODE of tourna * tourna

let rec parenize (tournament: tourna): string =
    match tournament with
    | LEAF team ->
        (
            match team with
            | Korea -> "Korea"
            | France -> "France"
            | Usa -> "Usa"
            | Brazil -> "Brazil"
            | Japan -> "Japan"
            | Nigeria -> "Nigeria"
            | Cameroon -> "Cameroon"
            | Poland -> "Poland"
            | Portugal -> "Portugal"
            | Italy -> "Italy"
            | Germany -> "Germany"
            | Norway -> "Norway"
            | Sweden -> "Sweden"
            | England -> "England"
            | Argentina -> "Argentina"
        )
    | NODE (t1, t2) -> Printf.sprintf "(%s %s)" (parenize t1) (parenize t2)

(* let () = print_endline (parenize( NODE(NODE(NODE(NODE(LEAF Argentina, LEAF Germany), NODE(LEAF Usa, LEAF Brazil)), NODE(NODE(LEAF Cameroon, LEAF England), NODE(LEAF Portugal, LEAF Norway))), NODE(NODE(NODE(LEAF Nigeria, LEAF Italy), NODE(LEAF Poland, LEAF Japan)), NODE(NODE(LEAF France, LEAF Korea), LEAF Sweden))))) *)