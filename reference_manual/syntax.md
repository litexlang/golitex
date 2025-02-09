Program
Statements
|-- KnowStatement
    |-- KnowBlock
        |-- Keyword: "know"
        |-- Colon: ":"
        |-- IndentedBlock
            |-- []FactStatement
    |-- KnowInline
        |-- Keyword: "know"
        |-- FactStatement
|-- TypeDeclaration
    |-- TypeDeclInline
        |-- TypeName
        |-- ?ImplementationClause
            |-- ImplementationKeyword: "impl"
            |-- ImplementationConceptName
    |-- TypeDeclBlock
        |-- MemberBlock
            |-- []MemberStatement
        |-- TypeMemberBlock
            |-- []MemberStatement
        |-- FactBlock
            |-- []FactStatement
