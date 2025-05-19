mod variables;
mod block;
mod builder;

#[cfg(test)]
mod tests {
    use hvergelmir_parser::{lexer::{lexer, CharStream}, syntax::{ast::definition::{File, FunctionDefinition}, stream::TokenStream, ParsingContext}};
    use string_interner::DefaultStringInterner;

    use crate::builder::BlockBuilderContext;

    #[test]
    fn file_blockify_test() {
        let mut symbols = DefaultStringInterner::new();
        let lexed = lexer(CharStream::new(r"
        
        func epic() {
            let x = ((2 + 5) * 3) + 4
            x = x + 1
            while x < 5 {
                x = x + 1
            }
            return x
        }
        
        "), &mut symbols).unwrap();
        let mut ts = TokenStream::new(&lexed, symbols);

        let mut file = ts.parse_one::<File>(&ParsingContext {}).unwrap();
        use enum_downcast::EnumDowncast;
        let b = BlockBuilderContext::default().make_blocks(file.definitions.remove(0).enum_downcast::<FunctionDefinition>().unwrap().block);

        

        panic!("{}", b.graphviz());

    }
}