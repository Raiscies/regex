
/*
	Regular Expression Interpreter by Raiscies.
	
	Supported Grammer:
	concat
	alter            | 
	parens            ()
	kleene closure    *
	positive closure  +
	optional          ?
	wildcard          .
	brackets          [...], [^...]
	braces            {m} {m,} {m,n}

*/

#include <map>
#include <set>
#include <list>
#include <stack>
#include <queue>
#include <vector>
#include <string>
#include <limits>
#include <memory>
#include <cstddef>
#include <cassert>
#include <utility>
#include <iterator>
#include <optional>
#include <iostream>
#include <functional>
#include <string_view>
#include <type_traits>
#include <unordered_map>

#include "fmt/core.h"
#include "fmt/ranges.h"

namespace rais {

namespace regex {

using std::cin;
using std::map;
using std::set;
using std::get;
using std::list;
using std::pair;
using std::swap;
using std::move;
using std::tuple;
using std::queue;
using std::stack;
using std::size_t;
using std::string;
using std::vector;
using std::optional;
using std::in_place;
using std::unique_ptr;
using std::string_view;
using std::basic_string;
using std::unordered_map;
using std::numeric_limits;
using std::underlying_type_t;
using std::reference_wrapper;
using std::basic_string_view;

template <typename CharT>
struct char_range {
	using char_t = CharT;
	char_t from, to;

	constexpr is_member(char_t c) const noexcept{
		return from <= c && c <= to;
	}
};

template <typename CharT>
constexpr bool in_range(CharT a, CharT b, CharT x) noexcept{ return a <= x && x <= b; }

template <typename CharT>
constexpr bool in_range(const char_range<CharT>& r, CharT x) noexcept { return r.is_member(x); }


enum class oper {
	// enum value represents the priority of the operators
	kleene,          // *
	positive,        // +
	optional,        // ?
	concat,          // (concatnation)
	alter,           // |
	lparen,          // (
	rparen,          // ) the priority of right-paren is meanless
	wildcard,        // . the priority of wildcard is meanless
	brackets,        // [chars...]
	brackets_invert, // [^chars...]
	braces           // {m}, {m,}, {m,n}
};

enum edge_category: char {
	epsilon     = 0, // empty edge
	single_char = 1, // range of one char [from]
	range       = 2, // range: [from-to]
	spaces      = 3, // space chars: [\f\n\r\t\v]
	words       = 4, // identifier chars(words): [0-9a-zA-Z_]
	digits      = 5, // digit chars: [0-9]
	newlines    = 6, // [\n\r](currently unused)
	all         = 7, // any chars


	// conjunction_range = 8, // a flag to mark the start state of this edge requires all of the edges it come from are accepted (conjunction)
	
	
	// // inverted ranges 
	invert_single_char = -single_char,  // [^c]
	invert_range       = -range,        // [^from-to]
	non_spaces         = -spaces,       // [^\f\n\r\t\v]
	non_words          = -words,        // [^0-9a-zA-Z_]
	non_digits         = -digits,       // [^0-9]
	
	non_newlines       = -newlines,     // [^\n\r] (wildcard)
	
	none               = -all,           // nothing could be accepted
	
	
	// some special edge, for internal implementation

	// identify the begin of sub-nfa, for capture grammer "(R)" 
	// greedy or not non-greedy, which are also epsilon edges
	// greedy_capture_begin = numeric_limits<underlying_type_t<edge_category>>::min(),        // (R)
	// nongreedy_capture_begin = numeric_limits<underlying_type_t<edge_category>>::min() + 1, 
};


// struct edge_category {

// 	bool is_invert: 1 = false;
// 	bool is_conjunction: 1 = false;
// 	range_category category: 6;
	
// 	constexpr edge_category(range_category category, bool is_invert = false, bool is_conjunction = false) noexcept: 
// 		is_invert{is_invert}, is_conjunction{is_conjunction}, category{category} {}

// 	static constexpr edge_category epsilon    () noexcept { return {epsilon}; }
// 	static constexpr edge_category single_char() noexcept { return {single_char}; }
// 	static constexpr edge_category range      () noexcept { return {range}; }
// 	static constexpr edge_category spaces     () noexcept { return {spaces}; }
// 	static constexpr edge_category words      () noexcept { return {words}; }
// 	static constexpr edge_category digits     () noexcept { return {digits}; }
// 	static constexpr edge_category newlines   () noexcept { return {newlines}; }
// 	static constexpr edge_category all        () noexcept { return {all}; }

// 	static constexpr edge_category exclude_single_char() noexcept { return {single_char, true}; }
// 	static constexpr edge_category exclude_range      () noexcept { return {range, true}; }
// 	static constexpr edge_category non_spaces         () noexcept { return {spaces, true}; }
// 	static constexpr edge_category non_words          () noexcept { return {words, true}; }
// 	static constexpr edge_category non_digits         () noexcept { return {digits, true}; }
// 	static constexpr edge_category non_newlines       () noexcept { return {newlines, true}; }
// 	static constexpr edge_category none               () noexcept { return {all, true}; }

// 	friend constexpr bool operator==(const edge_category l, const edge_category& r) noexcept {
// 		return l.category == r.category && l.is_invert == r.is_invert;
// 	}
// 	friend constexpr bool operator!=(const edge_category l, const edge_category& r) noexcept {
// 		return !(l == r);
// 	}

// 	constexpr edge_category& invert() noexcept {
// 		this->is_invert = !is_invert;
// 		return *this;
// 	}
// 	constexpr edge_category& set_conjunction(bool is_conjunction = true) noexcept {
// 		this->is_conjunction = is_conjunction;
// 		return *this;
// 	}
// };


template <typename CharT>
struct non_determinstic_automaton;

template <typename CharT> 
class nfa_builder {
	// a non-determinstic-finite-automaton factory
	// NFA M = (Q, Σ, δ, q0, F) 
	
	using char_t = CharT;
	using range_t = char_range<char_t>;
	using string_view_t = basic_string_view<char_t>;
	using string_iterator_t_t = typename string_view_t::const_iterator;

	using nfa_t = non_determinstic_automaton<char_t>;

	

	// using state_id_t = size_t;

	// using stateset_t = set<state_id_t>; // type of Q or Q's subset

	// indicate a sub nfa's complexity
	using complexity_t = size_t;
	static constexpr complexity_t default_unroll_complexity = 2000;
	complexity_t max_unroll_complexity = default_unroll_complexity;

	// vector<unique_ptr<state>> states;
	list<state> states;
	
	using state_iterator_t = typename list<state>::iterator;
	using state_const_iterator_t = typename list<state>::const_iterator;
	
	state_iterator_t final_state;
	vector<state_iterator_t> capture_groups; // capture groups' end state
	

	constexpr nfa_builder() {}

	struct edge;

	// internal representation(IR) of NFA state
	struct state {

		// out-going edges
		vector<edge> edges;
		bool is_conjunction = false;

		constexpr state() noexcept = default;
		constexpr state(bool is_conjunction) noexcept: 
			is_conjunction{is_conjunction} {}

		state* add_outgoing(const edge& e) {
			edges.push_back(e);
			return this;
		}

		state* set_conjunction(bool is_conjunction) {
			this->is_conjunction = is_conjunction;
			return this;
		}

	}; // state

	// internal representation(IR) of NFA::edge
	struct edge {
		edge_category category;
		state_iterator_t target; 

		union edge_data {
			// active when category == single_char
			char_t single_char; 
			// active when category == range
			range_t range;
			// active when category == epsilon
			size_t capture_group_id;
		} data; 

		constexpr edge(edge_category category, char_t single_char, state_iterator_t target = {}): 
			category{category}, target{target}, data{single_char} {}

		constexpr edge(edge_category category, range_t range, state_iterator_t target = {}): 
			category{category}, target{target}, data{range} {}

		constexpr edge(edge_category category, state_iterator_t target = {}): 
			category{category}, target{target} {}

	private:

		constexpr edge(edge_category category, edge_data data, state_iterator_t target = {}):
			category{category}, target{target}, data{data} {}

	public:

		constexpr edge() noexcept = default;
		constexpr edge(const edge&) noexcept = default;
		constexpr edge(const edge& other, state_iterator_t target) noexcept: 
			category{other.category}, target{target}, data{other.data} {}

		static constexpr edge make_epsilon(state_iterator_t target = {}) noexcept{
			return {edge_category::epsilon, target};
		}

		static constexpr edge make_single_char(char_t c, state_iterator_t target = {}) noexcept{
			return {edge_category::single_char, c, target};
		}

		static constexpr edge make_range(range_t range, state_iterator_t target = {}) noexcept{
			return {edge_category::range, range, target};
		}

		static constexpr edge make_capture(size_t capture_group_id, state_iterator_t target = {}) noexcept{
			return {edge_category::epsilon, capture_group_id, target};
		}

		edge& set_target(state_iterator_t target) noexcept{
			this->target = target;
			return *this;
		}

		edge& invert() noexcept{
			category = edge_category(-static_cast<underlying_type_t<edge_category>>(category));
			return *this;
		}


	}; // edge

	struct subnfa {
		edge begin_edge;
		state_iterator_t end_state;
		complexity_t complexity;

		constexpr subnfa(const edge& begin_edge, state_iterator_t end_state, complexity_t complexity) noexcept: 
			begin_edge{begin_edge}, end_state{end_state}, complexity{complexity} {}

		constexpr subnfa(const subnfa&) noexcept = default;


	};
	
	static constexpr int priority(oper op) noexcept{
		switch(op) {
		case oper::kleene   : 
		case oper::positive :
		case oper::optional : 
		case oper::brackets :
		case oper::brackets_invert:
		case oper::braces   :  
			return 0;
		case oper::concat   : return -1;
		case oper::alter    : return -2;
		case oper::lparen   : return -3;
		default: return -114514;
		}
	}

	enum error_category {
		success = 0,
		empty_pattern, 
		empty_operand, 
		bad_escape, 
		missing_paren,
		bad_bracket_expression,
		bad_brace_expression,
		expensive_brace_expression_unroll
	};


	static constexpr oper to_oper(char_t c) noexcept{
		switch(c) {
		case '*': return oper::kleene;
		case '+': return oper::positive;
		case '?': return oper::optional;
		case '|': return oper::alter;
		case '(': return oper::lparen;
		case ')': return oper::rparen;
		case '.': return oper::wildcard;
		default: return oper(-1);
		}
	}

	static constexpr string_view error_message(error_category category) noexcept{
		switch(category) {
		case success:                return "successed";
		case empty_operand:          return "empty operand";
		case bad_escape:             return "bad escape";
		case missing_paren:          return "missing parentheses";
		case bad_bracket_expression: return "bad bracket expression";
		case bad_brace_expression:   return "bad brace expression";
		case expensive_brace_expression_unroll: return "brace expression is too complex to unroll";
		}
		return "";
	}


protected:
	
	stack<subnfa, vector<subnfa>> nfa_stack;
	stack<oper>	oper_stack;

public:

	void reset() {
		states.clear();
		final_state = nullptr;
	}

	template <typename... Args>
	state_iterator_t new_state(Args&&... args) {
		// return states.emplace_back(std::make_unique<state>(args...)).get();
		states.emplace_back(args...);
		return --states.end();
	}
	template <typename... Args>
	state_iterator_t insert_new_state(state_terator_t it, Arg&&... args) {
		return states.insert(it, {args...});
	}

	// reduce current sub-nfa and then push to stack, 
	// or pop stack top sub-nfa, reduce it with current sub-nfa, and then push back to stack
	bool reduce() {
		return reduce(oper_stack.top());
	}

	bool reduce(oper op) {
		
		switch(op) {
			// unary operator *, ψ(R*) = ψ(R) + 1
			case oper::kleene: {
				if(nfa_stack.empty()) return false;
				auto& [begin_edge, end_state, complexity] = nfa_stack.top();
				
				end_state->add_outgoing(begin_edge);
				begin_edge = edge::make_epsilon(end_state);
				complexity += 1;
				
				break;
			}
			// unary operator +, ψ(R+) = ψ(R) + 1
			case oper::positive: { 
				if(nfa_stack.empty()) return false;
				auto& [begin_edge, end_state, complexity] = nfa_stack.top();
				
				end_state->add_outgoing(begin_edge);
				complexity += 1;
				break;
			}
			// unary operator ?, ψ(R?) = ψ(R) + 2
			case oper::optional: {
				if(nfa_stack.empty()) return false;
				auto& [begin_edge, end_state, complexity] = nfa_stack.top();
				
				auto state = new_state();
				state->add_outgoing(begin_edge)
				     ->add_outgoing(edge::make_epsilon(end_state));
					 
				begin_edge = edge::make_epsilon(state);
				complexity += 2;
				
				break;
			}
			// implicit binary oeprator concatenation, ψ(R1 R2) = ψ(R1) + ψ(R2)
			case oper::concat: {
				if(nfa_stack.size() < 2) return false;
				auto [begin_edge, end_state, complexity] = nfa_stack.top();
				nfa_stack.pop();
				// previous sub-nfa
				auto& [pre_begin_edge, pre_end_state, pre_complexity] = nfa_stack.top();
				
				pre_end_state->add_outgoing(begin_edge);
				pre_end_state = end_state;
				pre_complexity += complexity;
				
				break;	
			}
			// binary operator |, ψ(R1 | R2) = ψ(R1) + ψ(R2) + 3 
			case oper::alter: {
				// important: we must ensure states' order satisfy regular expression's order, 
				// which means we must adjust states's order in 'states' vector

				if(nfa_stack.size() < 2) return false;
				auto [begin_edge, end_state, complexity] = nfa_stack.top();
				nfa_stack.pop();

				// previous sub-nfa, we must pop it to access its pre-pre sub-nfa
				auto [pre_begin_edge, pre_end_state, pre_complexity] = nfa_stack.top();
				nfa_stack.pop();


				// the new branch_state must priviously be these two sub-nfa,
				// so we must insert it before the pre_start_state's target state 
				auto branch_state = insert_new_state(
					nfa_stack.empty() ? 
					states.begin() :
					std::next(nfa_stack.top().end_state)
				);

				branch_state->add_outgoing(pre_begin_edge)
					        ->add_outgoing(begin_edge);

				auto merge_state = new_state();
				pre_end_state->add_outgoing(edge::make_epsilon(merge_state));
				end_state->add_outgoing(edge::make_epsilon(merge_state));

				nfa_stack.emplace(
					edge::make_epsilon(branch_state), 
					merge_state, 
					pre_complexity + complexity + 3
				)

				break;
			}
			// left parentess (, ψ( (e) ) = ψ(e) + 1
			case oper::lparen: {
				if(nfa_stack.size() < 2) return false; 
				auto [begin_edge, end_state, complexity] = nfa_stack.top();
				nfa_stack.pop();

				auto& [capture_begin_edge, dummy_state, cap_complexity] = nfa_stack.top();
				dummy_state->add_outgoing(begin_edge);
				capture_groups[capture_begin_edge.data.capture_group_id] = end_state;
				
				cap_complexity += complexity;
				break;
			}

			default: {
				return false;
			}
		}
	}

	optional<edge> lex_escape(string_iterator_t& pos, const string_iterator_t& end) {

		/*
		character escapes::
		1. control escape
		2. c + control letter
		3. x + hex escape sequence
		4. identity escape
		// unsupported yet. 5. u + unicode escape sequence

			control escape:
				f: U+000C, page-feed
				n: U+000A, line-feed
				r: U+000D, return
				t: U+0009, tab
				v: U+000B, vertical-tab
			
			c + control letter:
				any upper/lower case ASCII character
				value = value_of_encode_unit / 32

			x + hex escape sequence:
				letter x and EXECTLY follow by two hex-digits

			identity escape:
				escape and other character that is not a letter or digit,
				such as \\, \.

			special escapes of re:
				d: digit
				D: non-digit
				s: space
				S: non-space
				w: letter, digit or '_'
				W: different from letter, digit or '_' 
	
		*/
		// assume pos != end
		switch(*pos++) {
		// control escapes:
		case 'f': return { edge_category::single_char, '\f' };
		case 'n': return { edge_category::single_char, '\n' };
		case 'r': return { edge_category::single_char, '\r' };
		case 't': return { edge_category::single_char, '\t' };
		case 'v': return { edge_category::single_char, '\v' };
		case '0': return { edge_category::single_char, '\0' };
		case 'b': return { edge_category::single_char, '\b' }; // backspace // TODO: this works only when in bracket expression, in other situation, this is a block identify character

		case 'c': {
			if(pos != end) {
				return { edge_category::single_char, char_t(*pos++ % 32) };
			}else {
				// bad escape
				return { std::nullopt };
			}
		}
		case 'x': {
			if(pos != end) {
				auto val = hex_val(*pos++);
				if((pos + 1) != end) {
					return { edge_category::single_char, char_t(val * 0x10 + hex_val(*pos++)) };
				}else {
					// actually it's a bad escape
					return { edge_category::single_char,  char_t(val) };
				}
			}else {	
				// it is also a bad escape
				++pos;
				return { std::nullopt };
			}
		}

		case 'd': return { edge_category::digits     };
		case 'D': return { edge_category::non_digits };
		case 's': return { edge_category::spaces     }; 
		case 'S': return { edge_category::non_spaces };
		case 'w': return { edge_category::words      };
		case 'W': return { edge_category::non_words  };

		}
		// idenitity escapes
		return { edge_category::single_char. *pos };

	}

	pair<error_category, const char_t*> parse(string_view_t s) {
		// shunting yard algorithm
		// operator priority:  *  > (concatnation) > |
		// supported operator: 
		// *,  |, (concatnation), ., 
		
		reset();
		
		if(s.empty()) return {empty_pattern, nullptr};

		bool has_potential_concat_oper = false;
		
		for(auto pos = s.begin(); pos != s.end();) {
			switch(*pos) {
			case '*': // kleene closure
			case '+': // positive closure, (r)+ ::= (r)(r)*
			case '?': // optional,         (r)? ::= (r)|ε

				// *, +, ? have the highest priorities, so directly reduce it
				if(!reduce(to_oper(*pos))) return {empty_operand, pos};
				++pos;
				has_potential_concat_oper = true;
				break;

			case '|':
				// alternative / 'or' operator
				while(!oper_stack.empty() && priority(oper_stack.top()) >= priority(oper::alter)) {
					if(!reduce()) return {empty_operand, pos};
					oper_stack.pop();
				}
				oper_stack.push(oper::alter);
				++pos;
				has_potential_concat_oper = false;
				break;

			case '(':
				if(has_potential_concat_oper && !reduce_concat()) return {empty_operand, pos};
				make_capture_group();
				oper_stack.push(oper::lparen);
				++pos;
				has_potential_concat_oper = false;
				break;

			case ')':
				while(!oper_stack.empty() && oper_stack.top() != oper::lparen) {
					if(!reduce()) return {empty_operand, pos};
					oper_stack.pop();
				}

				if(oper_stack.empty()) return {missing_paren, pos}; // error: missing left paren '('
				else {
					// the top must be lparen '(', reduce it to build a capture
					reduce();
					oper_stack.pop();
				}
				++pos;
				has_potential_concat_oper = true;
				break;

			case '[': {
				// [c...] bracket expression
				if(++pos == s.end()) return {bad_bracket_expression, pos};
				bool invert_range = false;
				if(*pos == '^') {
					invert_range = true;
					++pos;
				}
				if(auto brackets_res = parse_brackets(pos, s.end()); brackets_res.has_value()) {
					if(has_potential_concat_oper && !reduce_concat()) return {empty_operand, pos};

					if(!invert_range) reduce_brackets(brackets_res.value());
					else              reduce_brackets_invert(brackets_res.value()); 
				}else return {bad_bracket_expression, pos};
				
				has_potential_concat_oper = true;
				break;

			}
			case '{': {
				// {m}, {m,}, {m,n}  counted repetition expression
				auto braces_res = parse_braces(++pos, s.end());
				// get<0>(brace_res) is braces_case
				if(get<0>(braces_res) == 0) 
					return {bad_brace_expression, pos};
				if(!reduce_braces(braces_res)) 
					return {expensive_brace_expression_unroll, pos};
				has_potential_concat_oper = true;
				break;

			}
			default: {
				// is simple character(s)/wildcard
				edge e;
				switch(*pos) {
				case '\\':
					// escape
					if(auto lex_res = lex_escape(++pos, s.end()); lex_res.has_value()) 
						e = lex_res.value();
					else return {bad_escape, pos};
					// pos has been moved at lex_escape(), so don't need to ++pos;
					break;
				case '.':
					// . (wildcard)
					e = { edge_category::non_newlines };
					++pos;
					break;
				default:
					e = { edge_category::single_char ,*pos };
					++pos;
				}
				
				e.set_target(new_state());
				if(has_potential_concat_oper && !reduce_concat()) {
					return {empty_operand, pos};
				}
				// push char
				nfa_stack.emplace(e, e.target, 1);
				
				has_potential_concat_oper = true;
				break;
			} // default
			} // switch
		} // for

		// clear oper_stack
		while(!oper_stack.empty()) {
			if(oper_stack.top() == oper::lparen) {
				// missing right paren ')'
				return {missing_paren, s.end()};
			}else if(!reduce()) {
				return {empty_operand, s.end()};			
			}
			oper_stack.pop();
		}

		// is the element count of nfa_stack possible to be more then 1?
		assert(nfa_stack.size() == 1);

		// insert start state
		insert_new_state(states.begin())->add_outgoing(nfa_stack.top().begin_edge);
		final_state = nfa_stack.top().end_state;

		nfa_stack.clear();
		return {success, s.end()};
	}

	bool reduce_concat() {
		// insert a implicit concat operator
		while(!oper_stack.empty() && priority(oper_stack.top()) >= priority(oper::concat)) {
			if(!reduce()) return false;
			oper_stack.pop();
		}
		// empty oper_stack or oper_stack.top() < concat
		oper_stack.push(oper::concat);
		return true;
	}

	optional<vector<edge>> parse_brackets(string_iterator_t& pos, const string_iterator_t& end) {
		// assume pos is pointing at the first char after the left square bracket '[' and possible invert char '^' 

		vector<edge> edges;
		enum {
			parse_char, 
			parse_range, 
			parse_char_literally // treat '-' as a literal char
		} state = parse_char_literally;

		while(pos != end && *pos != ']') {
			if(state != parse_range) {
				// state == parse_char or parse_char_literally
				switch(*pos) {
				case '\\': 
					if(auto lex_res = lex_escape(++pos, end); lex_res.has_value()) {
						edges.push_back(lex_res.value());
					}else return { std::nullopt };
					state = parse_char;
					break;
				case '-':
					if(state == parse_char_literally) {
						edges.emplace_back(edge_category::single_char, '-');
						state = parse_char;
					}else {
						if(!edges.back().category == edge_category::single_char) 
							return { std::nullopt }; // bad char range like [\w-...]
						
						state = parse_range;
					}
					++pos;
					break;
				default:
					// chars
					edges.emplace_back(edge_category::single_char, *pos++);
					state = parse_char;
				}
			}else {
				// state == parse_range
				auto from = edges.back().data.single_char;

				switch(*pos) {
				case '\\': 
					if(auto lex_res = lex_escape(++pos, end); lex_res.has_value()) {
						if(!lex_res.value().category == edge_category::single_char) 
							return {}; // bad char range like: [c-\w]
						
						auto to = lex_res.value().data.single_char;
						// edges.back().set_range(edges.back().range.from, lex_res.value().range.from); 
						edges.back() = edge::make_range(from, to); // [p-\q]
					}else return { std::nullopt };
				default:
					// chars
					// parse_char_literally

					edges.back() = edge::make_range(from, *pos); // [p-q]
					++pos;
				}
				state = parse_char_literally;
			}
		}

		if(pos == end) return { std::nullopt }; // '...[', broken bracket 
		++pos; // skip ']'
		return std::move(edges);
	}

	void reduce_brackets(vector<edge>& edges) {
		auto post_state = new_state();
		if(edges.empty()) {
			// [], TODO: what does it means? 
			// none, newlines or something else?
			nfa_stack.emplace(edge{edge_category::none, post_state}, post_state, 1);
		}else if(edges.size() == 1) {
			// [r] == r
			nfa_stack.emplace(edges.front().set_target(post_state), post_state, 1);
		}else {
			// [R1...Rn]
			// new_e: -ε-> pre_state -{e1, e2, ...en}-> post_state

			auto pre_state = new_state();
			for(auto& e: edges) {
				pre_state->add_outgoing(e.set_target(post_state));
			}
			nfa_stack.emplace(edge::make_epsilon(pre_state), post_state, edges.size() + 1);
			
		}
	}

	void reduce_brackets_invert(nfa_stack_t& nfa_stack, vector<edge>& edges) {
		auto post_state = new_state();
		if(edges.empty()) {
			// [^], TODO: what does it means?
			// all, newlines or something else?
			nfa_stack.emplace(edge{edge_category::all, post_state}, post_state, 1);
		}else if(edges.size() == 1) {
			// [^r]
			// -^r-> post_state
			nfa_stack.emplace(edges.front().invert().set_target(post_state), post_state, 1);
		}else {
			// [^R1...Rn], this is a conjunction range, 
			// which means the target state(post_state) is accepted only if all of the edges(^R1, ^R2, ...) is accepted
			auto pre_state = new_state(true); // is_conjunction = true

			for(auto& e: edges) {
				pre_state->add_outgoing(e.set_target(post_state));
			}
			nfa_stack.emplace(edge::make_epsilon(pre_state), post_state, edges.size() + 1);

		}
	}

	size_t make_capture_group() { // return the capture group id 

		auto id = capture_groups.size();
		capture_groups.emplace_back({}); // currently no capture end state now

		auto dummy_state = new_state();
		edge capture_begin = edge::make_capture(id);
		dummy_state->add_outgoing(capture_begin, dummy_state);
		nfa_stack.emplace(capture_begin, dummy_state, 1);
		return id;
	}

	struct braces_result {
		enum kind_category {
			error = 0, 
			fixed, // {m} 
			left_bounded, // {m,}
			bounded, // {m, n}
		} kind;
		size_t down, up; // m, n

		static constexpr make_error() noexcept {
			return {error};
		}

		friend constexpr bool operator==(const braces_result& l, const braces_result& r) noexcept {
			if(l.kind == r.kind) {
				return l.kind == error || l.down == r.down && l.up == r.up;
			}else return false;
		} 
	};

	// counted loop 'R{n, m}' grammer
	bool reduce_braces(const braces_result& braces_res) {
		if(try_unroll_brace_expression(braces_res)) {
			return true;
		}
		// TODO: implement counted repetition loop? is it possible?
		// we probaly need to do something on the runtime machine, a 'stateful' state
		return false; 
	}

	// TODO: remake
	subnfa copy_subnfa(const subnfa& nfa) {
		// deep copy a sub-nfa
		// assume begin_edge and end_state are both valid
		// traverse the directed graph  -begin_edge-> ... > end_state
		// notice: if the source sub-nfa contains capture, 
		// at the runtime, the captured string will be reset on the next match
		// for example: (R){m}, it will only capture the last match string of R, but not m captures of each R match
		// this should be handle properly

		edge e_copy {e, new_state()};
		if(e.target == q) {
			// delta.m.emplace_back();
			for(auto& edge_from_q: delta.m[q]) {
				if(edge_from_q.target == q) 
					delta.m[e_copy.target].emplace_back(edge_from_q, e_copy.target);
			}
			return {e_copy, e_copy.target};
		}

		// delta.m.emplace_back(delta.m[e.target]); // index is e_copy.target
		delta.m[e_copy.target] = delta.m[e.target];

		map<state_id_t, state_id_t> memo{{e.target, e_copy.target}}; // [src_state_index] -> [copy_state_index]
		queue<state_id_t> que; 
		que.emplace(e_copy.target);
		state_id_t q_copy;
		while(!que.empty()) {
			auto copy = que.front();
			que.pop();
			
			// replace the target states
			for(auto& edge_from_copy: delta.m[copy]) {
				if(auto it = memo.find(edge_from_copy.target); it != memo.end()) {
					// don't need to create new state
					edge_from_copy.set_target(get<1>(*it));
				}else {
					// create new state
					state_id_t new_target = new_state(delta.m[edge_from_copy.target]);
					memo[edge_from_copy.target] = new_target; // register memo
					if(edge_from_copy.target != q)  // the edge list of the last state q should be copy at the end
						que.emplace(new_target);
					else 
						q_copy = new_target;
					edge_from_copy.set_target(new_target); // reset target
				}
			}
		}
		// copy the last state q
		// remove-erase idiom, note that the order of the edges are not important
		auto forward =   delta.m[q_copy].begin(),
		    backward = --delta.m[q_copy].end();
		while(forward != delta.m[q_copy].end()) {
			if(auto forward_res = memo.find(forward->target); forward_res != memo.end()) {
				forward->set_target(get<1>(*forward_res));
				++forward;
			}else {
				while(backward != forward) {
					if(auto backward_res = memo.find(backward->target); backward_res != memo.end()) {
						(*forward = *backward).set_target(get<1>(*backward_res));
						--backward;
						goto next_forward;
					}else --backward;
				}
				// backward == forward
				break;
				next_forward:
				++forward;
			}
		}
		delta.m[q_copy].erase(forward, delta.m[q_copy].end());
		
		return {e_copy, q_copy};
	}

	// TODO: remake
	bool try_unroll_brace_expression(const braces_result& braces_res) {
		// R{m}   == R...R            m times R
		// R{m,}  == R...R+           m times R
		// R{m,n} == R...R(R?)...(R?) m times R and n-m times R?, 
		// however, we use a slightly trickly way to implement but not directly unroll it

		// (R){m}  == R...(R)             m times R, but capture the last R, 
		// (R){m,} == R...(R)+            m times R, but capture the last R

		// (R){m,n} == R...(R)(R?)...(R?) m times R and n-m times R?, but capture the last R,
		// here the parentheses identify the same capture

		auto& [begin_edge, end_state, complexity] = nfa_stack.top();
		auto [kind, m, n] = braces_res;
		complexity_t new_complexity;

		// nfa_stack.pop();
		
		switch(kind) {
		case 3: // e{m,n}
			if(m != n) {
				new_complexity = n * complexity + n - m;
				if(new_complexity > max_unroll_complexity) return false;
				nfa_stack.pop();

				state_id_t current_q = q;
				state_id_t final_q = nfa.new_state();
				if(m != 0) {
					for(size_t i = 0; i <= m - 1; ++i) { // loop m - 1 times
						auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
						nfa.bind_transform(current_q, new_e);
						current_q = new_q;
					}
					nfa.bind_empty_transform(current_q, final_q);
					for(size_t i = 0; i < n - m; ++i) {
						auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
						nfa.bind_transform(current_q, new_e);
						nfa.bind_empty_transform(current_q, final_q);
						current_q = new_q;
					}
				}else {
					edge front_e = {nfa.new_state()};
					nfa.bind_empty_transform(front_e.target, final_q);
					nfa.bind_transform(front_e.target, e);
					nfa.bind_empty_transform(current_q, final_q);
					for(size_t i = 0; i < n - 1; ++i) { // n != m => n != 0
						auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
						nfa.bind_transform(current_q, new_e);
						nfa.bind_empty_transform(new_q, final_q);
						current_q = new_q;
					}
					e = front_e;
				}
				nfa_stack.emplace(e, final_q, new_complexity);
				break;
			} 
			// else m == n: e{m,m} = e{m}
			[[fallthrough]];
		case 1: // e{m}
			if(m == 0) {
				// e{0} == ε
				// simply ignore the edge e 
				nfa_stack.pop();
				nfa_stack.emplace(edge{q}, q, 1); // -ε-> q
			}else {
				new_complexity = psi * m;
				if(new_complexity > max_unroll_complexity) return false;
				nfa_stack.pop();

				state_id_t current_q = q;
				for(size_t i = 0; i < m - 1; ++i) {
					auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
					nfa.bind_transform(current_q, new_e);
					current_q = new_q;
				}
				nfa_stack.emplace(e, current_q, new_complexity);
			}
			break;
		case 2: // e{m,}
			if(m == 0) {
				// e{0,} == e*
				nfa_stack.pop();
				nfa.bind_transform(q, e);                // q -e->...> q
				nfa_stack.emplace(edge{q}, q, psi + 1);  // -ε-> q
			}else {
				// e{m,} == e ... e+
				new_complexity = (m + 1) * psi;
 				if(new_complexity > max_unroll_complexity) return false;
				nfa_stack.pop();

				state_id_t current_q = q;
				for(size_t i = 0; i < m - 1; ++i) {
					auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
					nfa.bind_transform(current_q, new_e);
					current_q = new_q;
				}
				nfa.bind_transform(current_q, edge{e, current_q});
				nfa_stack.emplace(e, current_q, new_complexity);
			}
			break;
		}
		return true;

	}


	braces_result parse_braces(string_iterator_t& pos, const string_iterator_t& end) {
		// m, n ::= [0-9]+
		auto lex_digits = [end](auto& p) {
			size_t n = 0;
			do{ n = n * 10 + size_t(*p++ - '0'); }while(p != end && in_range('0', '9', *p));
			return n;
		};

		braces_result::kind_category kind = braces_result::error;
		size_t m, n = 0;
		while(pos != end && *pos != '}') {
			// if(*pos == ' ') {++pos; continue;} // spaces are not allowed
			switch(kind) {
			case braces_result::error: 
				// lex the first arg: m
				if(in_range('0', '9', *pos)) {
					m = lex_digits(pos);
					kind = braces_result::fixed;
				}else return braces_result::make_error(); // bad expression
				break;
			case braces_result::fixed:
				// lex comma: ,
				if(*pos != ',') return braces_result::make_error(); // bad expression
				++pos;
				// ++parse_stete;
				kind = braces_result::left_bounded;
				break;
			case braces_result::left_bounded:
				// lex the next arg: n
				if(in_range('0', '9', *pos)) {
					if(n = lex_digits(pos); m > n) return braces_result::make_error(); // {m, n}, m > n
					kind = braces_result::bounded;
				}else return braces_result::make_error();// bad expression
				break;
			default:
				return braces_result::make_error(); // bad expression
			}
		}
		if(pos == end) return braces_result::make_error();
		// finished lexing braces expression
		++pos;
		return {kind, m, n};
	}

private:

	static constexpr int hex_val(char_t x) noexcept{
		if('0' <= x && x <= '9') {
			return x - '0';
		}else if('a' <= x && x <= 'f') {
			return (x - 'a') + 10;
		}else {
			// 'A' <= x && x <= 'F'
			return (x - 'A') + 10;
		}
	}

	nfa_t generate() {

	}

}; // nfa_builder

template <typename CharT>
struct non_determinstic_finite_automaton {
	// a non-determinstic-finite-automaton(NFA)


	// NFA M = (Q, Σ, δ, q0, F) 
	using char_t = CharT; // Σ
	using string_view_t = basic_string_view<char_t>;
	using range_t = char_range<char_t>;

	using state_id_t = size_t;

	using state_set_t = set<state_id_t>; // type of Q or Q's subset

	using final_state_set_t = state_set_t; // F: is a subset of Q

	using result_t = vector<string_view_t>;

	struct edge {
		

		edge_category category;
		
		union{
			// active when category == single_char
			char_t single_char; 
			// active when category == range
			range_t range;
			// active when category == epsilon
			state_id_t capture_end;
		};


		state_id_t target = -1;

		constexpr edge(state_id_t target = -1) noexcept: 
			category{edge_category::epsilon}, target{target} {} // an empty(epsilon) edge

		constexpr edge(edge_category category_, state_id_t target = -1) noexcept: 
			category{category_}, target{target} {}

		constexpr edge(char_t c, bool invert_range_ = false, state_id_t target = -1) noexcept: 
			category{invert_range_ ? edge_category::invert_single_char : edge_category::single_char}, single_char{c}, target{target} {}
			
		constexpr edge(char_t from_, char_t to_, bool invert_range_ = false, state_id_t target = -1) noexcept: 
			category{invert_range_ ? edge_category::invert_range : edge_category::range}, range{from_, to_}, target{target} {}
		
		constexpr edge(const edge&) noexcept = default;
		constexpr edge(const edge& other, state_id_t target) noexcept: edge{other} {
			target = target;
		}

	private:
		constexpr edge(bool greedy, state_id_t target, state_id_t capture_end_) noexcept:
			category{greedy ? edge_category::greedy_capture_begin : edge_category::nongreedy_capture_begin}, 
			capture_end{capture_end_}, 
			target{target} {}
	public:

		static constexpr edge make_epsilon(state_id_t target = -1) noexcept{
			return {target};
		}

		// static constexpr edge make_capture(bool greedy, state_id_t target, state_t capture_end) noexcept{
		// 	return {greedy, target, capture_end};
		// }
		static constexpr edge make_conjunction(state_id_t target = -1) noexcept{
			return {edge_category::conjunction_range, target};
		}
		

		bool accept(char_t c) const noexcept{
			switch(category) {
			case edge_category::epsilon: 
			// case edge_category::greedy_capture_begin:
			// case edge_category::nongreedy_capture_begin:
				return false; 
			case edge_category::single_char: // range of one char [from]
				return c == single_char;
			case edge_category::range:       // range: [from-to]
				return in_range(range, c);
			case edge_category::spaces:      // space chars: [\t\n\v\f\r] == [\x09-\x0d]
				return in_range('\x09', '\x0d', c);
			case edge_category::words:       // identifier chars(words): [0-9a-zA-Z_]
				return in_range('0', '9', c) || 
				       in_range('a', 'z', c) || 
				       in_range('A', 'Z', c) || 
				       (c == '_');
			case edge_category::digits:      // digit chars: [0-9]
				return in_range('0', '9', c);
			case edge_category::newlines:
				return c == '\n' || c == '\r';
			case edge_category::all:
				return true;
			// invert ranges 
			case edge_category::non_newlines:       // [^\n\r]
				return c != '\n' && c != '\r';
			case edge_category::invert_single_char: // [^c]
				return c != single_char;
			case edge_category::invert_range:       // [^from-to]
				return !in_range(range, c);
			case edge_category::non_spaces:         // [^\t\n\v\f\r]
				return !in_range('\x09', '\x0d', c);
			case edge_category::non_words:          // [^0-9a-zA-Z_]
				return not( 
					in_range('0', '9', c) || 
			    	in_range('a', 'z', c) || 
			    	in_range('A', 'Z', c) || 
			    	(c == '_'));
			case edge_category::non_digits:         // [^0-9]
				return !in_range('0', '9', c);
			case edge_category::none:
				return false;
			default:
				return false;
			}

		}
		bool accept_epsilon() const noexcept{
			switch(category) {
				case edge_category::epsilon:
				// case edge_category::greedy_capture_begin:
				// case edge_category::nongreedy_capture_begin:
					return true;
				default: 
					return false;
			} 	
		}
		edge& set_target(state_id_t index) noexcept{
			target = index;
			return *this;
		}

		edge& set_range(char_t from_, char_t to_, bool invert_range_ = false) noexcept{
			// from = from_;
			// to = to_;
			range = {from_, to_};
			category = invert_range_ ? edge_category::invert_range : edge_category::range;
			return *this;
		}
		edge& set_range(char_t c, bool invert_range_ = false) noexcept{
			single_char = c;
			category = invert_range_ ? edge_category::invert_single_char : edge_category::single_char;
			return *this;
		}
		edge& set_range(edge_category category_) noexcept{
			category = category_;
			return *this;
		}


		edge& invert() noexcept{
			category = edge_category(-static_cast<underlying_type_t<edge_category>>(category));
			return *this;	
		}
		bool is_single_char() const noexcept{
			return category == edge_category::single_char;
		}
		bool is_conjunction_range() const noexcept{
			return category == edge_category::conjunction_range;
		}

		// bool is_capture_start() const noexcept{
		// 	return category == edge_category::greedy_capture_begin || 
		// 	       category == edge_category::nongreedy_capture_begin;
		// }

		// bool is_greedy_capture() const noexcept{
		// 	return category == edge_category::greedy_capture_begin;
		// }
		// bool is_non_greedy_capture() const noexcept{
		// 	return category == edge_category::nongreedy_capture_begin;
		// }

	}; // struct edge


	// stores the contexts of captures in running nfa
	struct capture_contexts {

		capture_contexts() = default;

		struct capture_context_item {
			const edge& begin;  // the begin of a sub-nfa
			const state_id_t end;  // the end of a sub-nfa
			const bool greedy;

			const char_t* capture_begin = nullptr, 
			            * capture_end = nullptr;
			bool completed = false;

			constexpr capture_context_item(const edge& begin_, const char_t* capture_begin_ = nullptr) noexcept: begin{begin_}, end{begin_.capture_end}, greedy{begin.is_greedy_capture()}, capture_begin{capture_begin_} {}

			constexpr capture_context_item() noexcept {}

			void reset_capture(const char_t* new_begin = nullptr) noexcept{
				capture_begin = new_begin;
				capture_end = nullptr;
				completed = false;
			}

			void complete_capture(const char_t* end) noexcept{
				if(!completed or greedy) {
					capture_end = end;
					completed = true;
				}
			}

			string_view_t get_capture() const noexcept{
				if(capture_begin != nullptr && capture_end != nullptr) 
					// capture_begin is pointing to the position that ahead of the first char of the capture
					return {capture_begin + 1, static_cast<size_t>(capture_end - capture_begin)};
				else 
					return {};
			}

		}; 

		unordered_map<const edge*, capture_context_item> contexts;
		unordered_map<state_id_t, capture_context_item*> contexts_ref_by_state;

		bool new_context(const edge& e, const char_t* capture_begin = nullptr) {
			auto [it, inserted] = contexts.try_emplace(&e, e, capture_begin);
			if(inserted) {
				contexts_ref_by_state.try_emplace(e.capture_end, &it->second);
			}

			return inserted;
		}

		// reset context by the edge if it's already exists, or else create a new context
		void reset_capture(const edge& e, const char_t* capture_begin = nullptr) {
			if(not new_context(e, capture_begin)) {
				contexts.at(&e).reset_capture(capture_begin);
			}
		}

		void reset_all_captures() {
			// reset all of the capture items
			for(capture_context_item& ctx: contexts) {
				ctx.reset_capture();
			}
		}

		// always assume the arguments are valid 

		bool try_complete_capture(const edge& e, const char_t* capture_end) {
			if(contexts.count(&e) != 0) {
				contexts.at(&e).complete_capture(capture_end);
				return true;
			}
			return false;
		}
		bool try_complete_capture(state_id_t end_state, const char_t* capture_end) {
			if(contexts_ref_by_state.count(end_state) != 0) {
				contexts_ref_by_state[end_state]->complete_capture(capture_end);
				return true;
			}
			return false;
		}

		capture_context_item& get_context(const edge& e) {
			return contexts.at(&e);
		}
		capture_context_item& get_context(state_id_t end_state) {
			return *contexts_ref_by_state[end_state];
		}

		result_t get_result() const{
			result_t captures;
			for(auto& kv: contexts) {
				const capture_context_item& context = kv.second;
				// auto& [eptr, context] = kv;
				if(context.completed) 
					captures.push_back(context.get_capture());
			}
			return captures;
		}

	}; // struct capture_contexts


	// δ: Q * (Σ ∪ {ε}) -> 2^Q
// 	struct transformer {

// 		// accept (state-space(q), {character-space(c)}) -> {state-space(q)}
// 		vector<vector<edge>> m;

// 		// capture_context context;

// 		// do_epsilon_closure, without capture_contexts
// 		state_set_t& do_epsilon_closure(state_set_t& current_states) const{
// 			// do ε-closure(current_states) and assign to itself
// 			state_set_t current_appended_states = current_states, 
// 			               next_appended_states;
// 			while(true) {
// 				for(state_id_t q: current_appended_states) {
// 					for(const edge& e: m[q]) {
// 						if(e.accept_epsilon() && current_states.count(e.target) == 0) {
// 							// e links to a new state that does not in current_states set
// 							next_appended_states.insert(e.target);

// 						}
// 					}
// 				}
// 				if(next_appended_states.empty()) return current_states;

// 				current_states.insert(next_appended_states.begin(), next_appended_states.end());
// 				current_appended_states = std::move(next_appended_states);
// 				next_appended_states.clear();
// 			}
// 		}

// 		state_set_t& do_epsilon_closure(state_set_t& current_states, const char_t* pos, capture_contexts& contexts) const{
// 			// do ε-closure(current_states) and assign to itself
// 			state_set_t current_appended_states = current_states, 
// 			               next_appended_states;
// 			while(true) {
// 				for(state_id_t q: current_appended_states) {
// 					for(const edge& e: m[q]) {
// 						if(e.accept_epsilon() && current_states.count(e.target) == 0) {
// 							// e links to a new state that does not in current_states set
// 							next_appended_states.insert(e.target);

// 							// handle capture
// 							if(e.is_capture_start()) {
// 								contexts.reset_capture(e, pos);
// 							}
// 						}
// 					}
// 				}
// 				if(next_appended_states.empty()) return current_states;

// 				current_states.insert(next_appended_states.begin(), next_appended_states.end());
// 				current_appended_states = std::move(next_appended_states);
// 				next_appended_states.clear();
// 			}
// 		}

// 		// without capture_contexts
// 		state_set_t operator()(const state_set_t& current_states, char_t c) const{
// 			// assume ε-closure(current_states) == current_states

// 			if(current_states.empty()) return {};
// 			state_set_t new_states;

// 			for(auto q: current_states) {
// 				// for each protential current state
// 				if(m[q].empty()) continue;
// 				else if(auto first_edge = m[q][0]; first_edge.is_conjunction_range()) {
// 					// this state and its edges are conjunction
// 					// c is accepted only when all of the edges are accepted 
// 					for(auto it = ++m[q].cbegin(); it != m[q].cend(); ++it)
// 						if(!it->accept(c)) goto next_state;

// 					// this conjunction range is accepted
// 					new_states.insert(first_edge.target);

// 					next_state:;
// 				}else {
// 					for(const edge& e: m[q]) {
// 						// for each range
// 						if(e.accept(c)) {
// 							new_states.insert(e.target);
// 						}
// 					} 
// 				}
// 			}
// 			return new_states;
// 			// return do_epsilon_closure(new_states);
// 		}

		state_set_t operator()(const state_set_t& current_states, const char_t* pos, capture_contexts& contexts) const{
				// assume ε-closure(current_states) == current_states

			if(current_states.empty()) return {};
			state_set_t new_states;
			char_t c = *pos;

			for(auto q: current_states) {
				// for each protential current state
				if(m[q].empty()) continue;
				else if(auto first_edge = m[q][0]; first_edge.is_conjunction_range()) {
					// this state and its edges are conjunction
					// c is accepted only when all of the edges are accepted 
					for(auto it = ++m[q].cbegin(); it != m[q].cend(); ++it)
						if(!it->accept(c)) goto next_state;

					// this conjunction range is accepted
					new_states.insert(first_edge.target);
					contexts.try_complete_capture(first_edge.target, pos);

					next_state:;
				}else {
					for(const edge& e: m[q]) {
						// for each range
						if(e.accept(c)) {
							new_states.insert(e.target);

							// try to complete the state if it is a end state of a sub nfa,
							// or else do nothing.
							contexts.try_complete_capture(e.target, pos);
						}
					} 
				}
			}
			// does not do_epsilon_closure anymore
			return new_states;
			// return do_epsilon_closure(new_states, pos, contexts);
		}

// 	}; // struct transformer

// private:
// 	state_id_t max_state_index = 0;

// public:
// 	// static constexpr state_id_t trap_state = state_id_t(-1);

// 	transformer delta;
// 	final_state_set_t final_states;

	// non_determinstic_automaton() {
	// 	new_state();	
	// }

	// void reset() {
	// 	delta.m.clear();
	// 	final_states.clear();
	// 	max_state_index = 0;
	// 	delta.m.emplace_back();
	// }

	// state_id_t new_state() {
	// 	delta.m.emplace_back();
	// 	return ++max_state_index;
	// }
	// state_id_t new_state(const vector<edge>& edges) {
	// 	delta.m.emplace_back(edges);
	// 	return ++max_state_index;
	// }

	// void mark_final_state(state_id_t index) {
	// 	final_states.insert(index);
	// }

	// bool bind_transform(state_id_t index, state_id_t target_index, const edge& e) {
	// 	if(index > max_state_index or target_index > max_state_index) return false;

	// 	delta.m[index].push_back(e.set_target(target_index)); // reset target
	// 	return true;
	// }
	// bool bind_transform(state_id_t index, const edge& e) {
	// 	if(index > max_state_index) return false;

	// 	delta.m[index].push_back(e);
	// 	return true;
	// }
	// bool bind_empty_transform(state_id_t index, state_id_t target_index) {
	// 	if(index > max_state_index or target_index > max_state_index) return false;
	// 	delta.m[index].emplace_back(target_index);
	// 	return true;
	// }


	// only check if the target is acceptable, but not capture anything 
	bool test(string_view_t target, state_set_t start_states = {0}) const{
		if(start_states.empty()) return false;

		state_set_t current_states = std::move(delta.do_epsilon_closure(start_states));

		for(const auto c: target) {
			// move to the next state set
			auto new_states = delta(current_states, c);
			// do ε-closure
			delta.do_epsilon_closure(current_states);

			if(new_states.empty()) return false; // this nfa does not accept target string
			current_states = std::move(new_states);
		}
		// check if (current_states ∪ F) != Φ
		for(auto q: current_states) {
			if(final_states.count(q) != 0) return true; // target was accepted
		}
		return false; // target is unacceptable

	}

	// // try to match the whole target and capture sub strings
	// result_t match(string_view_t target) const{

	// 	// init capture contexts
	// 	capture_contexts contexts;

	// 	state_set_t current_states = {0};

	// 	auto pos = target.cbegin();
	// 	delta.do_epsilon_closure(current_states, pos - 1, contexts);

	// 	for(; pos != target.cend(); ++pos) {
	// 		// move to the next state set
	// 		auto new_states = delta(current_states, pos, contexts);
	// 		// an then do ε-closure
	// 		delta.do_epsilon_closure(new_states, pos, contexts);
	// 		if(new_states.empty()) return {}; // nothing to match
	// 		current_states = std::move(new_states);
	// 	}

	// 	for(auto q: current_states) {
	// 		if(final_states.count(q) != 0) return contexts.get_result();
	// 	}

	// 	return {}; // target is unacceptable

	// }

	// result_t search(string_view_t target) const{

	// 	capture_contexts contexts;

	// 	state_set_t current_states;

	// 	// naive!
	// 	for(auto s = target.cbegin(); s != target.cend();) {
	// 		current_states.emplace(0);

	// 		auto pos = s;

	// 		delta.do_epsilon_closure(current_states, pos, contexts);

	// 		for(; pos != target.cend(); ++pos) {
	// 			auto new_states = delta(current_states, *pos);
	// 			if(new_states.empty()) {
	// 				// not return false, but let s move to the next char, 
	// 				// and try to match again
	// 				goto next_pass;
	// 			}

	// 			current_states = std::move(new_states);
	// 		}
	// 		// once the regex is matched, stop matching the tailing strings and return the result
	// 		for(auto q: current_states) {
	// 			if(final_states.count(q) != 0) return contexts.get_result();
	// 		}

	// 		next_pass:
	// 		// reset all of state set and contexts
	// 		contexts.reset_all_captures();
	// 		current_states.clear();
	// 		++s;
	// 	}

	// 	return {};
	// }

	// // single step test
	// state_set_t step(char_t c, state_set_t start_states) const{
	// 	return delta(delta.do_epsilon_closure(start_states), c);
	// }

	// // single step match
	// state_set_t step(const char_t* pos, state_set_t start_states, capture_contexts& contexts) const{
	// 	return delta(delta.do_epsilon_closure(start_states), pos, contexts);
	// }


}; // struct non_determinstic_automaton

template <typename CharT>
using NFA = non_determinstic_automaton<CharT>;

template <typename CharT>
struct regular_expression {
	using char_t = CharT;
	using string_t = basic_string<char_t>;
	using string_view_t = basic_string_view<char_t>;

	// store the pattern capture result
	// using capture_t = vector<string_view_t>; 
	
	using complexity_t = size_t;

	using nfa_builder_t = nfa_builder<char_t>;

	// using edge = typename nfa_t::edge;
	// using state_id_t = typename nfa_t::state_id_t;

	/*	sub expression(e) complexity(ψ) algorithm:
		e = 
			R or [] or [R] or [^] or [^R]   (R is a single range/edge)
			             : ψ(e) = 1
			[R1R2...Rn]  : ψ(e) = n + 1               (n > 1)
			[^R1R2...Rn] : ψ(e) = n + 2               (n > 1)
			e1 | e2      : ψ(e) = ψ(e1) + ψ(e2) + 3
			e1 e2        : ψ(e) = ψ(e1) + ψ(e2)
			e1*          : ψ(e) = ψ(e1) + 1
			e1+          : ψ(e) = 2ψ(e1)
			e1?          : ψ(e) = ψ(e1) + 2
			e1{m}        : ψ(e) = mψ(e1)              (if ψ(e) <= max_unroll_complexity)
			e1{m,}       : ψ(e) = (m + 1)ψ(e1)        (if ψ(e) <= max_unroll_complexity)
			e1{m,n}      : ψ(e) = nψ(e1) + (n - m)    (if ψ(e) <= max_unroll_complexity)

		if ψ(e) <= max_unroll_complexity: 
			using trivial unroll algorithm: 
				e{m}   -> e...e for m times e;
				e{m,}  -> e...e+ for m times e;
				e{m,n} -> e...e(e?...e?) for m times e and n - m times (e?)
		else: 
			using loop algorithm for the sub expression. 
	*/

	//parsing output: NFA M = (Q, Σ, δ, q0, F) 
	

	regular_expression(string_view_t pattern) {
		parse(pattern);
	}
	regular_expression() noexcept = default;

	auto parse(string_view_t pattern) {
		nfa_builder_t builder();
		builder.parse(pattern);
	}

	

}; // struct regular_expression

} // namespace regex

} // namespace rais

int main(int argc, const char** argv) {
	
	using namespace fmt;
	using namespace rais::regex;


	while(true) {
		
		string pattern = "";
		
		print("input a pattern:\n");
		cin >> pattern;

		print("pattern: {}\n", pattern);

		// regular_expression<char> re;
		
		// auto [parse_result, pos] = re.parse(pattern);
		
		// print("pattern result: {}\n", re.error_message(parse_result));
		
		// if(parse_result != regular_expression<char>::error_category::success) continue;

		// while(true) {
		// 	string target;
		// 	print("input a target string:\n");
		// 	cin >> target;
		// 	if(target == "~") break;
		// 	bool passed_test = re.nfa.test(target);
		// 	auto result = re.nfa.match(target);
		// 	print("target = {}, test result = {}, capture: {}\n", target, passed_test, result);
		// }
		
	}

	return 0;
}