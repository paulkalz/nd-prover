use crate::formula::Formula;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Atom(String),
    Not,        // !
    And,        // &
    Or,         // v
    Implies,    // ->
    Equivalent, // <->
    LParen,     // (
    RParen,     // )
    Turnstile,  // |-
    Comma,      // ,
}

// Input-string -> Vector of Tokens
fn tokenize(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next(); // Ignoriere whitespace
            }
            '(' => { tokens.push(Token::LParen); chars.next(); }
            ')' => { tokens.push(Token::RParen); chars.next(); }
            ',' => { tokens.push(Token::Comma); chars.next(); }
            '&' => { tokens.push(Token::And); chars.next(); }
            'v' => { tokens.push(Token::Or); chars.next(); }
            '!' => { tokens.push(Token::Not); chars.next(); }
            '-' => {
                chars.next();
                if chars.peek() == Some(&'>') {
                    chars.next();
                    tokens.push(Token::Implies);
                } else {
                    panic!("Unexpected character after '-': {:?}", chars.peek());
                }
            }
            '<' => {
                chars.next();
                if chars.next() == Some('-') && chars.peek() == Some(&'>') {
                    chars.next();
                    tokens.push(Token::Equivalent);
                } else {
                    panic!("Unexpected character after '<': {:?}", chars.peek());
                }
            }
            '|' => {
                chars.next();
                if chars.peek() == Some(&'-') {
                    chars.next();
                    tokens.push(Token::Turnstile);
                } else {
                    panic!("Unexpected character after '|': {:?}", chars.peek());
                }
            }
            _ if c.is_alphabetic() => {
                let mut name = String::new();
                name.push(chars.next().unwrap()); 
                
                while let Some(&next_c) = chars.peek() {
                    if next_c.is_alphanumeric() {
                        name.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Atom(name));
            }
            _ => panic!("Unexpected character in Input: {}", c),
        }
    }
    tokens
}


pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(input: &str) -> Self {
        Parser {
            tokens: tokenize(input),
            pos: 0,
        }
    }

    // looks at token at current pos
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    // consumes the current token, when it matches the expected type
    fn match_token(&mut self, expected: Token) {
        if let Some(t) = self.peek() {
            if *t == expected {
                self.pos += 1;
                return;
            }
        }
        panic!("Expected token {:?}, instead found {:?}", expected, self.peek());
    }

    // recursively parses a list of tokens, returns a formula
    pub fn parse_formula(&mut self) -> Formula {
        match self.peek() {
            Some(Token::Atom(name)) => {
                let atom_name = name.clone();
                self.pos += 1;
                Formula::Atom(atom_name)
            }
            Some(Token::Not) => {
                self.pos += 1;
                let inner = self.parse_formula();
                Formula::Not(Box::new(inner))
            }
            Some(Token::LParen) => {
                self.pos += 1; // consumes '('
                
                // parse left side
                let left = self.parse_formula();
                
                // find junctor
                let junctor = match self.peek() {
                    Some(Token::And) => Token::And,
                    Some(Token::Or) => Token::Or,
                    Some(Token::Implies) => Token::Implies,
                    Some(Token::Equivalent) => Token::Equivalent,
                    _ => panic!("Expected binary junctor, found {:?}", self.peek()),
                };
                self.pos += 1; // consume junctor
                
                // parse right side
                let right = self.parse_formula();
                
                self.match_token(Token::RParen); // consume ')'
                
                match junctor {
                    Token::And => Formula::And(Box::new(left), Box::new(right)),
                    Token::Or => Formula::Or(Box::new(left), Box::new(right)),
                    Token::Implies => Formula::Implies(Box::new(left), Box::new(right)),
                    Token::Equivalent => Formula::Equivalent(Box::new(left), Box::new(right)),
                    _ => unreachable!(),
                }
            }
            _ => panic!("Syntaxerrror: Unexpected start of a formula at: {:?}", self.peek()),
        }
    }

    // parses the entire input-string
    pub fn parse_input(&mut self) -> (Vec<Formula>, Formula) {
        let mut premises = Vec::new();
        
        if self.peek() != Some(&Token::Turnstile) { // if the first token is not "|-", we have premises
            loop {
                premises.push(self.parse_formula());
                match self.peek() {
                    Some(Token::Comma) => {
                        self.pos += 1; // consume ',' continue with the next premise
                    }
                    Some(Token::Turnstile) => {
                        break;
                    }
                    _ => panic!("Expected ',' or '⊦' after premise, found {:?}", self.peek()),
                }
            }
        }
        
        self.match_token(Token::Turnstile); // consume '|-'
        
        let conclusion = self.parse_formula();
        
        (premises, conclusion)
    }
}

/// Parses an input-string. Returns (Vec(Premises), Conclusion).
pub fn parse(input: &str) -> (Vec<Formula>, Formula) {
    let mut parser = Parser::new(input);
    parser.parse_input()
}







// Unit tests


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize_simple() {
        let tokens = tokenize("P, Q |- (P & Q)");
        assert_eq!(tokens.len(), 9);
        assert_eq!(tokens[0], Token::Atom("P".to_string()));
        assert_eq!(tokens[1], Token::Comma);
        assert_eq!(tokens[2], Token::Atom("Q".to_string()));
        assert_eq!(tokens[3], Token::Turnstile);
        assert_eq!(tokens[4], Token::LParen);
        assert_eq!(tokens[5], Token::Atom("P".to_string()));
        assert_eq!(tokens[6], Token::And);
        assert_eq!(tokens[7], Token::Atom("Q".to_string()));
        assert_eq!(tokens[8], Token::RParen);
    }

    #[test]
    fn test_tokenize_alternatives() {
        let tokens = tokenize("P |- !Q");
        assert_eq!(tokens[0], Token::Atom("P".to_string()));
        assert_eq!(tokens[1], Token::Turnstile);
        assert_eq!(tokens[2], Token::Not);
        assert_eq!(tokens[3], Token::Atom("Q".to_string()));
    }

    #[test]
    fn test_tokenize_complex_atoms() {
        let tokens = tokenize("P1, Q12 |- !R3");
        assert_eq!(tokens[0], Token::Atom("P1".to_string()));
        assert_eq!(tokens[2], Token::Atom("Q12".to_string()));
        assert_eq!(tokens[4], Token::Not);
        assert_eq!(tokens[5], Token::Atom("R3".to_string()));
    }

    #[test]
    fn test_tokenize_whitespace_independence() {
        let tokens_dense = tokenize("P|-(!Q&R)");
        let tokens_loose = tokenize("P   |-   ( ! Q   &   R )");
        assert_eq!(tokens_dense, tokens_loose);
    }

    #[test]
    fn test_parse_nested_negations() {
        let mut parser = Parser::new("!!!P");
        let formula = parser.parse_formula();
        
        let expected = Formula::Not(Box::new(Formula::Not(Box::new(Formula::Not(Box::new(
            Formula::Atom("P".to_string())
        ))))));
        assert_eq!(formula, expected);
    }

    #[test]
    fn test_parse_all_binary_operators() {
        let operators = vec![("&", "And"), ("v", "Or"), ("->", "Implies"), ("<->", "Equivalent")];
        
        for (op, type_str) in operators {
            let input = format!("(P {} Q)", op);
            let mut parser = Parser::new(&input);
            let formula = parser.parse_formula();
            
            match (type_str, formula) {
                ("And", Formula::And(l, r)) => {
                    assert_eq!(*l, Formula::Atom("P".to_string()));
                    assert_eq!(*r, Formula::Atom("Q".to_string()));
                },
                ("Or", Formula::Or(l, r)) => {
                    assert_eq!(*l, Formula::Atom("P".to_string()));
                    assert_eq!(*r, Formula::Atom("Q".to_string()));
                },
                ("Implies", Formula::Implies(l, r)) => {
                    assert_eq!(*l, Formula::Atom("P".to_string()));
                    assert_eq!(*r, Formula::Atom("Q".to_string()));
                },
                ("Equivalent", Formula::Equivalent(l, r)) => {
                    assert_eq!(*l, Formula::Atom("P".to_string()));
                    assert_eq!(*r, Formula::Atom("Q".to_string()));
                },
                _ => panic!("Operator {} was parsed incorrectly.", op),
            }

        }
    }

    #[test]
    fn test_parse_no_premises() {
        let mut parser = Parser::new("|- (P v !P)");
        let (premises, conclusion) = parser.parse_input();
        
        assert!(premises.is_empty());
        assert_eq!(
            conclusion,
            Formula::Or(
                Box::new(Formula::Atom("P".to_string())),
                Box::new(Formula::Not(Box::new(Formula::Atom("P".to_string()))))
            )
        );
    }

    #[test]
    fn test_parse_multiple_premises() {
        let mut parser = Parser::new("(P & Q), !R, S |- T");
        let (premises, conclusion) = parser.parse_input();
        
        assert_eq!(premises.len(), 3);
        assert_eq!(conclusion, Formula::Atom("T".to_string()));
        
        // check first premise
        if let Formula::And(l, _r) = &premises[0] {
            assert_eq!(**l, Formula::Atom("P".to_string()));
        } else {
            panic!("Premise wrong.");
        }
    }


    #[test]
    #[should_panic(expected = "Expected binary junctor, found Some(Atom(\"Q\"))")]
    fn test_panic_missing_operator() {
        let mut parser = Parser::new("(P Q)");
        parser.parse_formula();
    }

    #[test]
    #[should_panic(expected = "Expected ',' or '⊦' after premise, found Some(Atom(\"Q\"))")]
    fn test_panic_malformed_premises_separator() {
        let mut parser = Parser::new("P Q |- R");
        parser.parse_input();
    }
}