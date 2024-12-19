%option noyywrap
%{
/*****************声明和选项设置  begin*****************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "syntax_tree.h"
#include "syntax_analyzer.h"

int lines;
int pos_start;
int pos_end;

void pass_node(char *text){
     yylval.node = new_syntax_tree_node(text);
}

/*****************声明和选项设置  end*****************/

%}
%x comment
letter [a-zA-Z]
digit [0-9]
id {letter}+
integer {digit}+
floatt ({digit}+".")|({digit}*"."{digit}+)
irrelevant [\t]+|[\r]+|[" "]+ 

%%
 /* to do for students */
 /* two cases for you, pass_node will send flex's token to bison */
\n {lines++;}
\+ 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return ADD;}
\- 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return MINUS;}
\* 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return MULTIPLY;}
\/ 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return DIVIDE;}
\< 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return LESSTHAN;}
\> 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return GREATERTHAN;}
\; 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return SEMICOLONS;}
\, 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return COMMA;}
\( 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return LEFTPARENTHESIS;}
\) 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return RIGHTPARENTHESIS;}
\[ 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return LEFTSQUAREBRACKET;}
\] 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return RIGHTSQUAREBRACKET;}
\{ 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return LEFTCURLYBRACKET;}
\} 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return RIGHTCURLYBRACKET;}
\= 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return EQUAL;}
"<=" 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return LESSOREQUALTHAN;}
">=" 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return GREATEROREQUALTHAN;}
"==" 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return EQUALTO;}
"!=" 	{pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return NOTEQUALTO;}
"else" {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return ELSE;}
"if"  {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return IF;}
"int"  {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return INT;}
"return"  {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return RETURN;}
"void" {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return VOID;}
"while"  {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return WHILE;}
"float"  {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return FLOAT;}
{floatt}  {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return FLOATPOINT;}
{integer} {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return INTEGER;}
{id} {pos_start = pos_end; pos_end += strlen(yytext); pass_node(yytext); return ID;}
{irrelevant} {}
"/*" BEGIN(comment);
<comment>[^*\n]*        
<comment>"*"+[^*/\n]*   
<comment>\n     
<comment>"*"+"/" BEGIN(INITIAL); 

. { pos_start = pos_end; pos_end++; return ERROR; }

 /****请在此补全所有flex的模式与动作  end******/
 
%%