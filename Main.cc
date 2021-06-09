#include "cp_lib/string.cc"
#include "cp_lib/io.cc"
#include "cp_lib/algorithm.cc"
#include <stdlib.h>

using namespace cp;


enum struct Token_Type {
    literal,
    number,
    arrow,
    new_line,
    count
};

struct Token {
    Token_Type type;
    str text;

    u32 line_number;
    u32 line_char_number;
};

void print(Token token) {
    if (token.type != Token_Type::new_line) {
        printf("(%i, %.*s)", (i32)token.type, token.text.cap, token.text.buffer);
    } else {
        printf("(%i, \\n)", (i32)token.type);
    }
}

inline bool is_space(char c) {
    return (c == ' ' || c == '\t' || c == '\n');
}
inline bool is_digit(char c) {
    return ('0' <= c && c <= '9');
}
inline bool is_lc_letter(char c) {
    return ('a' <= c && c <= 'z');
}
inline bool is_uc_letter(char c) {
    return ('A' <= c && c <= 'Z');
}
inline bool is_letter(char c) {
    return is_lc_letter(c) || is_uc_letter(c);
}
inline bool is_alphanumeric(char c) {
    return is_digit(c) || is_letter(c);
}
inline bool is_literal_symbol(char c) {
    return is_alphanumeric(c) || c == '\\';
}


void skip_spacing(darr<Token> *out_tokens, buff_iter<char> *it, buff_iter<char> end, u32 *out_line_number, u32 *out_line_char_number) {
    while (*it != end && is_space(*it->ptr)) {
        if (*it->ptr == '\n') {
            push(out_tokens, {Token_Type::new_line, str{it->ptr, 1}, *out_line_number, *out_line_char_number});
            (*out_line_number)++;
            (*out_line_char_number) = 0;
        }
        (*out_line_char_number)++;
        (*it)++;
    } 
}

namespace Debug {
    void error(const char* msg) {
        printf("Error) %s\n", msg);
    }
    void tokenize_error(u32 line_number, u32 line_char_number, const char* msg) {
        printf("Error (l:c) %u:%u) %s\n", line_number, line_char_number, msg);
    }
}

bool tokenize(darr<Token> *out_tokens, str text) {
    u32 line_number = 1;
    u32 line_char_number = 1;
    auto it = begin(&text);
    for (; it != end(&text);) {
        skip_spacing(out_tokens, &it, end(&text), &line_number, &line_char_number);
        if (it == end(&text))
            return true;
        //if (is_digit(*it)) {
            //Debug::tokenize_error(line_number, line_char_number, "Invalid literal (starts with a digit)");
            //return false;
        //}
        if (is_literal_symbol(*it)) {
            str token_text = {it.ptr, 0};
            while (is_literal_symbol(*it) && it != end(&text)) {
                token_text.cap++;
                line_char_number++;
                it++;
            }
            push(out_tokens, {Token_Type::literal, token_text, line_number, line_char_number});
            continue;
        }
        if (*it == '-' && it + 1 != end(&text)) {
            line_char_number++;
            if (*(it + 1) == '>') {
                push(out_tokens, {Token_Type::arrow, str{it.ptr, 2}, line_number, line_char_number});
                line_char_number++;
                it += 2;
            } else {
                Debug::tokenize_error(line_number, line_char_number, "Invalid literal (wanted arrow)");
                return false;
            }
            continue;
        }

        Debug::tokenize_error(line_number, line_char_number, "Unknown symbol");
        return false;
    }
    return true;
}

/* grammar: 
 
state literal arrow state literal direction
terminals: {[a-z], [A-Z], [0-9], L, R, N, ->}
non-terminals: {Expr, Literal, State, Direction}

<Z> -> [a-z] | [A-Z] | [0-9]
<D> -> [0-9]
<Letter> -> <Z> | <Z><Letter> 
<Number> -> <D> | <D><Number>

<Literal> -> <Letter>
<State> -> q<Number>
<Direction> -> L | R | N
<Expr> -> <State> <Z> \-\> <State> <Z> <Direction>

*/

struct State_Transition {
    u32 lstate_index;
    str lstate_token;

    struct Transiton {
        u32 rstate_index;
        str rstate_token;
        
        str lsymbol;
        str rsymbol;
        str step;

        u32 line_number;
    };
    darr<Transiton> transitions;
};

bool operator==(const State_Transition& f, const State_Transition& s) {
    return f.lstate_index == s.lstate_index;
}

bool state_transition_lstate_token_eq_lmd(State_Transition f, State_Transition s) {
    return f.lstate_token == s.lstate_token;
}

darr<State_Transition> tm_program_table;

u32 state_index(str token, darr<State_Transition> *out_tm_program_table) {
    auto find_it = find(begin(out_tm_program_table), end(out_tm_program_table), {.lstate_token = token}, state_transition_lstate_token_eq_lmd);
    if (!find_it) {
        push(out_tm_program_table, {len(out_tm_program_table), token});
        find_it = {&back(out_tm_program_table)};
    }
    return find_it.ptr - beginp(out_tm_program_table);
}

bool gen_tm_program_table(darr<State_Transition> *out_tm_program_table, darr<Token> tokens) 
{
    bool q0_found = false;
    for (auto it = begin(&tokens); it != end(&tokens);) {
        while (it->type == Token_Type::new_line && it != end(&tokens)) {
            it++;
        }
        if (it == end(&tokens))
            return true;
        if (0 < endp(&tokens) - it.ptr && endp(&tokens) - it.ptr < 5) {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Invalid program");
            return false;
        }

        u32 line_number = it->line_number;
        if (it->type != Token_Type::literal || it->text[0] != 'q') {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Expected state");
            return false;
        }
        if (len(&it->text) == 2) { 
            if (it->text[1] == '0') {
                q0_found = true;
            } else if (it->text[1] == 'f') {
                Debug::tokenize_error(it->line_number, it->line_char_number, "Final state at the left side");
                return false;  
            }
        }
        u32 lstate_index = state_index(it->text, out_tm_program_table);
        str lstate_token = it->text;
        it++;

        if (it->type != Token_Type::literal) {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Expected character");
            return false;
        }
        str lsymbol = it->text;
        it++;

        if (it->type != Token_Type::arrow) {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Expected arrow operator");
            return false;
        }
        it++;

        if (it->type != Token_Type::literal || it->text[0] != 'q') {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Expected state");
            return false;
        }
        u32 rstate_index = (it->text != str{"qf"}) ? state_index(it->text, out_tm_program_table) : -1;
        str rstate_token = it->text;
        it++;

        if (it->type != Token_Type::literal) {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Expected character");
            return false;
        }
        str rsymbol = it->text;
        it++;

        if (it->type != Token_Type::literal || len(&it->text) != 1) {
            Debug::tokenize_error(it->line_number, it->line_char_number, "Expected direction");
            return false;
        }
        str step;
        switch(it->text[0]) {
            case 'L': { step = "-1"; } break;
            case 'N': { step = "0"; } break;
            case 'R': { step = "1"; } break;

            default: {
                 Debug::tokenize_error(it->line_number, it->line_char_number, "Expected direction");
                 return false;
            } break;
        }
        it++;

        // update table
        auto find_it = find(out_tm_program_table, State_Transition{lstate_index}).ptr;
        if (!find_it) {
            push(out_tm_program_table, {lstate_index, lstate_token});
            find_it = &back(out_tm_program_table);
        }
        push(&find_it->transitions, {rstate_index, rstate_token, lsymbol, rsymbol, step, line_number});
    }
    
    if (!q0_found) {
        Debug::error("q0 not found (no entry point)");
        return false;
    }

    return true;
}

str c_sourse_begin_formated = {R"(
char tape[10];
char* ptr = &tape[5];
int main() {
    tape[5] = 'a';
)"};

str c_sourse_end_formated = {R"(
    qe: return 1;
    qf: return 0;
}
)"};

str c_sourse_begin = {"char tape[10]={};char* ptr = &tape[5];int main() {\n"};

str c_sourse_end = {"qe: return 1; qf: return 0;}"};

bool gen_c_source_formated(dstrb *out_text, darr<State_Transition> tm_program_table, str file_name) {
    dstrb sb; init(&sb);
    for (auto it = begin(&tm_program_table); it != end(&tm_program_table); it++) {
        cat(&sb, pack(str{"\t"}, it->lstate_token, str{":; switch (*ptr) {\n"}));
        for (auto tr_it = begin(&it->transitions); tr_it != end(&it->transitions); tr_it++) {
            // provide debug info #line <line> "<file>"

            // char format[] = "if (*ptr == %c) {*ptr = %c; ptr += %i; goto %.*s;}";
            auto ts = pack(str{"\t\tcase '"}, tr_it->lsymbol, "': { *ptr = '", tr_it->rsymbol, "'; ptr += ", tr_it->step, "; goto ", tr_it->rstate_token, "; }break;\n" );
            cat(&sb, ts);
        }
        cat(&sb, pack(str{"\t\tdefault: {goto qf;}\n\t}\n"}));
    }
    cat(out_text, pack(c_sourse_begin, to_str(sb), c_sourse_end));
    return true;
}

bool gen_c_source(dstrb *out_text, darr<State_Transition> tm_program_table, str file_name) {
    dstrb sb; init(&sb);
    for (auto it = begin(&tm_program_table); it != end(&tm_program_table); it++) {
        if (len(&it->transitions) == 0) {
            cat(&sb, pack(it->lstate_token, str{": goto qf;\n"}));
            continue;
        }
        //debug info
        sstrb temp; to_str(&temp, begin(&it->transitions)->line_number);
        auto di_tokens = pack<str>("#line ", to_str(&temp), " \"", file_name, "\"\n");

        cat(&sb, di_tokens);
        cat(&sb, pack(it->lstate_token, str{": switch (*ptr) {\n"}));
        for (auto tr_it = begin(&it->transitions); tr_it != end(&it->transitions); tr_it++) {
            // provide debug info #line <line> "<file>"
            // char format[] = "if (*ptr == %c) {*ptr = %c; ptr += %i; goto %.*s;}";
            auto ts = pack<str>("#line ", to_str(&temp), " \"", file_name, "\"\n",
                "case '", tr_it->lsymbol, "': { *ptr = '", tr_it->rsymbol, "'; ptr += ", tr_it->step, "; goto ", tr_it->rstate_token, "; }break;\n" );
            cat(&sb, ts);
        }
        cat(&sb, pack(str{"default: {goto qe;}}\n"}));
    }
    cat(out_text, pack(c_sourse_begin, to_str(sb), c_sourse_end));
    return true;
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        Debug::error("No arguments provided");
        return 1;
    }

    dstrb text;
    if (!read_whole(&text, argv[1])) {
        Debug::error("Can't open file");
        return 1;
    } 

    darr<Token> tokens; init(&tokens);
    if (!tokenize(&tokens, to_str(text))) 
        return 1;
    print(&tokens);
    
    init(&tm_program_table, 1);
    rpush(&tm_program_table, {0, str{"q0"}});
    if (!gen_tm_program_table(&tm_program_table, tokens))
        return 1;

    dstrb c_sourse; init(&c_sourse);
    if (!gen_c_source(&c_sourse, tm_program_table, str{argv[1]}))
        return 1;
    //print(c_sourse);
    output_to_file("tm.c", c_sourse);
    system("g++ -g tm.c -o tm");

    return 0;
}
