use crate::token_block::TokenBlock;
use crate::parser::Parser;

#[test]
#[ignore]
fn tmp() {
    let code = "1 + 1 = 2\n$p(a, b)\nexist a R st {a > 0}";
    let blocks = TokenBlock::parse_blocks(code, 0).expect("parse blocks failed");
    let parser = Parser::new();
    for mut b in blocks {
        let stmt = parser.stmt(&mut b);
        if let Err(e) = stmt {
            println!("{}", e);
        } else {
            println!("{}\n", stmt.unwrap());
        }
    }
    println!("success! :)\n");
}