%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#include "syntax_tree.h"

// external functions from lex
extern int yylex();
extern int yyparse();
extern int yyrestart();
extern FILE * yyin;

// external variables from lexical_analyzer module
extern int lines;
extern char * yytext;
extern int pos_end;
extern int pos_start;

// Global syntax tree
syntax_tree *gt;

// Error reporting
void yyerror(const char *s);

// Helper functions written for you with love
syntax_tree_node *node(const char *node_name, int children_num, ...);
%}

/* TODO: Complete this definition.
   Hint: See pass_node(), node(), and syntax_tree.h.
         Use forward declaring. */
%union {
    struct _syntax_tree_node* node;
}

/* TODO: Your tokens here. */
%token <node> ERROR
%token <node> ADD
%token <node> ID
%token <node> SEMICOLONS
%token <node> LEFTSQUAREBRACKET
%token <node> RIGHTSQUAREBRACKET
%token <node> INTEGER
%token <node> INT
%token <node> FLOAT
%token <node> FLOATPOINT
%token <node> VOID
%token <node> LEFTPARENTHESIS
%token <node> RIGHTPARENTHESIS
%token <node> COMMA
%token <node> LEFTCURLYBRACKET
%token <node> RIGHTCURLYBRACKET
%token <node> IF
%token <node> ELSE
%token <node> WHILE
%token <node> RETURN
%token <node> LESSOREQUALTHAN
%token <node> LESSTHAN
%token <node> GREATERTHAN
%token <node> GREATEROREQUALTHAN
%token <node> EQUALTO
%token <node> NOTEQUALTO
%token <node> EQUAL
%token <node> MINUS
%token <node> MULTIPLY
%token <node> DIVIDE

%type <node> program
%type <node> declaration_list
%type <node> declaration
%type <node> var_declaration
%type <node> type_specifier
%type <node> fun_declaration
%type <node> params
%type <node> param_list
%type <node> param
%type <node> compound_stmt
%type <node> local_declarations
%type <node> statement_list
%type <node> statement
%type <node> expression_stmt
%type <node> selection_stmt
%type <node> iteration_stmt
%type <node> return_stmt
%type <node> expression
%type <node> var
%type <node> simple_expression
%type <node> relop
%type <node> additive_expression
%type <node> addop
%type <node> term
%type <node> mulop
%type <node> factor
%type <node> integer
%type <node> float_
%type <node> call
%type <node> args
%type <node> arg_list

%start program

%%
/* TODO: Your rules here. */

/* Example:
program: declaration-list {$$ = node( "program", 1, $1); gt->root = $$;}
       ;
*/

program : declaration_list {$$ = node("program", 1, $1); gt->root = $$;};
declaration_list : declaration_list declaration {$$ = node("declaration-list", 2, $1, $2);} | declaration {$$ = node("declaration-list", 1, $1);};
declaration : var_declaration {$$ = node("declaration", 1,$1);} | fun_declaration {$$ = node("declaration", 1,$1);};
var_declaration : type_specifier ID SEMICOLONS {$$ = node("var-declaration", 3, $1, $2, $3);} | type_specifier ID LEFTSQUAREBRACKET INTEGER RIGHTSQUAREBRACKET SEMICOLONS {$$ = node("var-declaration", 6, $1, $2, $3, $4, $5, $6);};
type_specifier : INT {$$ = node("type-specifier", 1, $1);} | FLOAT {$$ = node("type-specifier", 1, $1);} | VOID {$$ = node("type-specifier", 1, $1);};
fun_declaration : type_specifier ID LEFTPARENTHESIS params RIGHTPARENTHESIS compound_stmt {$$ = node("fun-declaration", 6, $1, $2, $3, $4, $5, $6);};
params : param_list {$$ = node("params", 1, $1);} | VOID {$$ = node("params", 1, $1);};
param_list : param_list COMMA param {$$ = node("param-list", 3, $1, $2, $3);} | param {$$ = node("param-list", 1, $1);};
param : type_specifier ID {$$ = node("param", 2, $1, $2);} | type_specifier ID LEFTSQUAREBRACKET RIGHTSQUAREBRACKET{$$ = node("param", 4, $1, $2, $3, $4);};
compound_stmt : LEFTCURLYBRACKET local_declarations statement_list RIGHTCURLYBRACKET {$$ = node("compound-stmt", 4, $1, $2, $3, $4);};
local_declarations : local_declarations var_declaration {$$ = node("local-declarations", 2, $1, $2);} | {$$ = node("local-declarations", 0);};
statement_list : statement_list statement  {$$ = node("statement-list", 2, $1, $2);} | {$$ = node("statement-list", 0);};
statement : expression_stmt {$$ = node("statement", 1, $1);} | compound_stmt {$$ = node("statement", 1, $1);} | selection_stmt {$$ = node("statement", 1, $1);} | iteration_stmt {$$ = node("statement", 1, $1);} | return_stmt {$$ = node("statement", 1, $1);}; 
expression_stmt : expression SEMICOLONS {$$ = node("expression-stmt", 2, $1, $2);} | SEMICOLONS {$$ = node("expression-stmt", 1, $1);};
selection_stmt : IF LEFTPARENTHESIS expression RIGHTPARENTHESIS statement {$$ = node("selection-stmt", 5, $1, $2, $3, $4, $5);} | IF LEFTPARENTHESIS expression RIGHTPARENTHESIS statement ELSE statement {$$ = node("selection-stmt", 7, $1, $2, $3, $4, $5, $6, $7);};
iteration_stmt : WHILE LEFTPARENTHESIS expression RIGHTPARENTHESIS statement {$$ = node("iteration-stmt", 5, $1, $2, $3, $4, $5);};
return_stmt : RETURN SEMICOLONS {$$ = node("return-stmt", 2, $1, $2);} | RETURN expression SEMICOLONS {$$ = node("return-stmt", 3, $1, $2, $3);};
expression : var EQUAL expression {$$ = node("expression", 3, $1, $2, $3);} | simple_expression {$$ = node("expression", 1, $1);};
var : ID {$$ = node("var", 1, $1);} | ID LEFTSQUAREBRACKET expression RIGHTSQUAREBRACKET {$$ = node("var", 4, $1, $2, $3, $4);};
simple_expression : additive_expression relop additive_expression {$$ = node("simple-expression", 3, $1, $2, $3);} | additive_expression {$$ = node("simple-expression", 1, $1);};
relop : LESSOREQUALTHAN {$$ = node("relop", 1, $1);} | LESSTHAN {$$ = node("relop", 1, $1);} | GREATERTHAN {$$ = node("relop", 1, $1);} | GREATEROREQUALTHAN {$$ = node("relop", 1, $1);} | EQUALTO {$$ = node("relop", 1, $1);} | NOTEQUALTO {$$ = node("relop", 1, $1);};
additive_expression : additive_expression addop term {$$ = node("additive-expression", 3, $1, $2, $3);} | term {$$ = node("additive-expression", 1, $1);};
addop : ADD {$$ = node("addop", 1, $1);} | MINUS {$$ = node("addop", 1, $1);};
term : term mulop factor {$$ = node("term", 3, $1, $2, $3);} | factor {$$ = node("term", 1, $1);};
mulop : MULTIPLY {$$ = node("mulop", 1, $1);} | DIVIDE {$$ = node("mulop", 1, $1);};
factor : LEFTPARENTHESIS expression RIGHTPARENTHESIS {$$ = node("factor", 3, $1, $2, $3);} | var {$$ = node("factor", 1, $1);}| call {$$ = node("factor", 1, $1);} | integer {$$ = node("factor", 1, $1);} | float_ {$$ = node("factor", 1, $1);}; 
integer : INTEGER {$$ = node("integer", 1, $1);};
float_ : FLOATPOINT {$$ = node("float", 1, $1);};
call : ID LEFTPARENTHESIS args RIGHTPARENTHESIS {$$ = node("call", 4, $1, $2, $3, $4);};
args : arg_list {$$ = node("args", 1, $1);} | {$$ = node("args", 0);};
arg_list : arg_list COMMA expression {$$ = node("arg-list", 3, $1, $2, $3);} | expression {$$ = node("arg-list", 1, $1);};

%%

/// The error reporting function.
void yyerror(const char * s)
{
    // TO STUDENTS: This is just an example.
    // You can customize it as you like.
    fprintf(stderr, "error at line %d column %d: %s\n", lines, pos_start, s);
}

/// Parse input from file `input_path`, and prints the parsing results
/// to stdout.  If input_path is NULL, read from stdin.
///
/// This function initializes essential states before running yyparse().
syntax_tree *parse(const char *input_path)
{
    if (input_path != NULL) {
        if (!(yyin = fopen(input_path, "r"))) {
            fprintf(stderr, "[ERR] Open input file %s failed.\n", input_path);
            exit(1);
        }
    } else {
        yyin = stdin;
    }

    lines = pos_start = pos_end = 1;
    gt = new_syntax_tree();
    yyrestart(yyin);
    yyparse();
    return gt;
}

/// A helper function to quickly construct a tree node.
///
/// e.g. $$ = node("program", 1, $1);
syntax_tree_node *node(const char *name, int children_num, ...)
{
    syntax_tree_node *p = new_syntax_tree_node(name);
    syntax_tree_node *child;
    if (children_num == 0) {
        child = new_syntax_tree_node("epsilon");
        syntax_tree_add_child(p, child);
    } else {
        va_list ap;
        va_start(ap, children_num);
        for (int i = 0; i < children_num; ++i) {
            child = va_arg(ap, syntax_tree_node *);
            syntax_tree_add_child(p, child);
        }
        va_end(ap);
    }
    return p;
}
