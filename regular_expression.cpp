
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
#include <algorithm>
#include <functional>
#include <string_view>
#include <type_traits>
#include <unordered_map>

#include "fmt/core.h"
#include "fmt/ranges.h"

namespace rais {

namespace regex {
	
enum class error_category {
	success = 0,
	ready, 
	empty_pattern, 
	empty_operand, 
	bad_escape, 
	missing_paren,
	bad_bracket_expression,
	bad_brace_expression,
	expensive_brace_expression_unroll
};


static constexpr std::string_view error_message(error_category category) noexcept{
	switch(category) {
	case error_category::success:                return "successed";
	case error_category::ready:                  return "ready to build";
	case error_category::empty_operand:          return "empty operand";
	case error_category::bad_escape:             return "bad escape";
	case error_category::missing_paren:          return "missing parentheses";
	case error_category::bad_bracket_expression: return "bad bracket expression";
	case error_category::bad_brace_expression:   return "bad brace expression";
	case error_category::expensive_brace_expression_unroll: return "brace expression is too complex to unroll";
	}
	return "";
}

namespace impl {

using std::list;
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
using std::basic_string_view;
using std::unordered_multimap;

template <typename CharT>
struct char_range {
	using char_t = CharT;
	char_t from, to;

	constexpr bool is_member(char_t c) const noexcept{
		return from <= c && c <= to;
	}
};

template <typename CharT>
constexpr bool in_range(CharT a, CharT b, CharT x) noexcept{ return a <= x && x <= b; }

template <typename CharT>
constexpr bool in_range(const char_range<CharT>& r, CharT x) noexcept { return r.is_member(x); }

// so dirty
template <typename CharT>
constexpr basic_string_view<CharT> make_string_view(const CharT* begin, const CharT* end) noexcept{
	return {&*begin, static_cast<size_t>(end - begin)};
}


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

	// inverted ranges 
	invert_single_char = -single_char,  // [^c]
	invert_range       = -range,        // [^from-to]
	non_spaces         = -spaces,       // [^\f\n\r\t\v]
	non_words          = -words,        // [^0-9a-zA-Z_]
	non_digits         = -digits,       // [^0-9]
	
	non_newlines       = -newlines,     // [^\n\r] (wildcard)
	
	none               = -all,           // nothing could be accepted
	
	

};

template <typename CharT>
struct non_determinstic_finite_automaton;

template <typename CharT> 
struct nfa_builder {
	// a non-determinstic-finite-automaton factory
	// NFA M = (Q, Σ, δ, q0, f) 
	
	/*	sub expression(e) complexity(ψ) algorithm:
		R = 
			R or [] or [R] or [^] or [^R]   (R is a single range/edge)
			             : ψ(R) = 1
			[R1R2...Rn]  : ψ(R) = n + 1               (n > 1)
			[^R1R2...Rn] : ψ(R) = n + 2               (n > 1)
			R1 | R2      : ψ(R) = ψ(R1) + ψ(R2) + 3
			R1 R2        : ψ(R) = ψ(R1) + ψ(R2)
			R1*          : ψ(R) = ψ(R1) + 1
			R1+          : ψ(R) = 2ψ(R1)
			R1?          : ψ(R) = ψ(R1) + 2
			R1{m}        : ψ(R) = mψ(R1)              (if ψ(R) <= max_unroll_complexity)
			R1{m,}       : ψ(R) = (m + 1)ψ(R1)        (if ψ(R) <= max_unroll_complexity)
			R1{m,n}      : ψ(R) = nψ(R1) + (n - m)    (if ψ(R) <= max_unroll_complexity)

		if ψ(R) <= max_unroll_complexity: 
			using trivial unroll algorithm: 
				R{m}   -> R...R for m times R;
				R{m,}  -> R...R+ for m times R;
				R{m,n} -> R...R(R?...R?) for m times R and n - m times (R?)
		else: 
			TODO: using loop algorithm for the sub expression. 
	*/

	
	using char_t = CharT;
	using range_t = char_range<char_t>;
	using string_view_t = basic_string_view<char_t>;
	using string_iterator_t = typename string_view_t::const_iterator;

	using nfa_t = non_determinstic_finite_automaton<char_t>;

	// using state_iterator_t = size_t;

	// using stateset_t = set<state_iterator_t>; // type of Q or Q's subset

	// indicate a sub nfa's complexity
	using complexity_t = size_t;
	
	using state_id_t = size_t;
	
	static constexpr complexity_t default_unroll_complexity = 2000;
	complexity_t max_unroll_complexity = default_unroll_complexity;


	
	constexpr nfa_builder() {}

	nfa_builder(string_view_t s) {
		parse(s);
	}
	
	struct edge;
	
	// internal representation(IR) of NFA state
	struct state {
		
		// out-going edges
		vector<edge> edges;
		bool is_conjunction = false;

		// this will be assigned after parsing
		state_id_t id;
		
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

		typename nfa_t::state generate() const{
			typename nfa_t::state s;
			for(const auto& e: edges) {
				s.edges.push_back(e.generate());
			}
			// do weed need this?
			s.is_conjunction = is_conjunction;
			return s;
		}
	}; // state

	// vector<unique_ptr<state>> states;
	list<state> states;
	
	using state_iterator_t = typename list<state>::iterator;
	using const_state_iterator_t = typename list<state>::const_iterator;

	// we must implement a hash function for state_iterator_t
	struct state_iterator_hash {
		// this function requires it is dereferenceable	
		constexpr size_t operator()(const state_iterator_t& it) const noexcept{
			return std::hash<const state*>()(&*it);
		}
	};

	state_iterator_t final_state;
	// vector<state_iterator_t> capture_groups; // capture groups' end state
	size_t max_capture_id = 0;
	

	// internal representation(IR) of NFA::edge
	struct edge {
		edge_category category;
		state_iterator_t target; 

		struct capture_info {
			size_t id = 0; // 0 means no capture
			state_iterator_t end;
		};
		union edge_data {
			// active when category == single_char
			char_t single_char; 
			// active when category == range
			range_t range;
			// active when category == epsilon
			capture_info capture;

			constexpr edge_data(): capture{} {}
			constexpr edge_data(char_t c): single_char{c} {}
			constexpr edge_data(range_t r): range{r} {}
			constexpr edge_data(capture_info cap): capture{cap} {}
		} data; 

		constexpr edge(edge_category category, char_t single_char, state_iterator_t target = {}) noexcept: 
			category{category}, target{target}, data{single_char} {}

		constexpr edge(edge_category category, range_t range, state_iterator_t target = {}) noexcept: 
			category{category}, target{target}, data{range} {}

		constexpr edge(edge_category category, state_iterator_t target = {}) noexcept: 
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
			return {edge_category::epsilon, capture_info{}, target};
		}

		static constexpr edge make_single_char(char_t c, state_iterator_t target = {}) noexcept{
			return {edge_category::single_char, c, target};
		}

		static constexpr edge make_range(range_t range, state_iterator_t target = {}) noexcept{
			return {edge_category::range, range, target};
		}

		static constexpr edge make_capture(size_t capture_group_id, state_iterator_t capture_end = {}, state_iterator_t target = {}) noexcept{
			return {edge_category::epsilon, capture_info{capture_group_id, capture_end}, target};
		}

		edge& set_target(state_iterator_t target) noexcept{
			this->target = target;
			return *this;
		}

		edge& invert() noexcept{
			category = edge_category(-static_cast<underlying_type_t<edge_category>>(category));
			return *this;
		}

		bool has_capture() const noexcept{
			return category == edge_category::epsilon && data.capture.id != 0;
		}

		edge& set_capture_end(state_iterator_t capture_end) {
			assert(has_capture());
			// if(has_capture()) 
			data.capture.end = capture_end;
			return *this;
		}
		edge& remove_capture() noexcept{
			// if(category == edge_category::epsilon) 
			assert(has_capture());
			data.capture.id = 0;
			return *this;
		}

		typename nfa_t::edge generate() const{
			
			typename nfa_t::edge res{
				category, 
				target->id
			};
			switch(category) {
				case edge_category::single_char: 
				case edge_category::invert_single_char:
					res.data.single_char = data.single_char;
					return res;
				case edge_category::range: 
				case edge_category::invert_range:
					res.data.range = data.range;
					return res;
				case edge_category::epsilon: 
					res.data.capture = typename nfa_t::capture_info {
						data.capture.id, 
						data.capture.id == 0 ? 0 : data.capture.end->id
					};
					return res;
				default:
					// whatever
					return res;
			}

		}

	}; // edge
	struct subnfa {
		edge begin_edge;

		// // all of the states between begin_state to end_state are belong to this sub-nfa, 
		// // notice: begin_state.target is gernally not equal to begin_state
		// state_iterator_t begin_state; // the state with the lowest index of the sub-nfa 
		state_iterator_t end_state;   // the state with the highest index of the sub-nfa

		complexity_t complexity;

		// constexpr subnfa(const edge& begin_edge, state_iterator_t begin_state, state_iterator_t end_state, complexity_t complexity) noexcept: 
		// 	begin_edge{begin_edge}, begin_state{begin_state}, end_state{end_state}, complexity{complexity} {}

		constexpr subnfa(const subnfa&) noexcept = default;
		constexpr subnfa(edge begin_edge, state_iterator_t end_state) noexcept: 
			begin_edge{begin_edge}, end_state{end_state} {}
		constexpr subnfa(edge begin_edge, state_iterator_t end_state, complexity_t complexity) noexcept: 
			begin_edge{begin_edge}, end_state{end_state}, complexity{complexity} {}


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


protected:
	
	// stack<subnfa, vector<subnfa>> nfa_stack;
	
	// we don't directly use stack cause sometimes we need to assess the 2th top element of the stack,
	// but don't want to pop the top, access it and push it back. 
	struct nfa_stack_t: public stack<subnfa, vector<subnfa>> {
		using stack_t = stack<subnfa, vector<subnfa>>;

		// it is UB if size() < 2
		constexpr typename stack_t::const_reference second_top() const{
			// return this->C[size() - 2]; 
			return *++this->c.crbegin(); // slightly released inner container constrain
		}
		constexpr typename stack_t::reference second_top() {
			// return this->C[size() - 2];
			return *++this->c.rbegin();
		}

		constexpr bool has_second_top() const noexcept{
			return this->size() >= 2;
		}

	} nfa_stack;

	stack<oper>	oper_stack;
	
	error_category build_result;
public:

	void reset() {
		states.clear();
		final_state = {};
		// capture_groups.clear();
		build_result = error_category::ready;
	}
	
	state_iterator_t top_begin_state() {
		assert(!nfa_stack.empty() && !states.empty());
		return nfa_stack.has_second_top() ? std::next(nfa_stack.second_top().end_state) : states.begin();
	}

	template <typename... Args>
	state_iterator_t new_state(Args&&... args) {
		// return states.emplace_back(std::make_unique<state>(args...)).get();
		states.emplace_back(args...);
		return --states.end();
	}
	template <typename... Args>
	state_iterator_t insert_new_state(state_iterator_t it, Args&&... args) {
		return states.insert(it, state{args...});
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
			// TODO: can it correctly handle capture?
			case oper::optional: {
				if(nfa_stack.empty()) return false;
				auto& [begin_edge, end_state, complexity] = nfa_stack.top();
				
				auto pre_state = insert_new_state(top_begin_state());
				pre_state->add_outgoing(begin_edge)
				     ->add_outgoing(edge::make_epsilon(end_state));
					 
				begin_edge = edge::make_epsilon(pre_state);
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
				auto& [pre_begin_edge, pre_end_state, pre_complexity] = nfa_stack.top();
				// nfa_stack.pop();


				// the new branch_state must priviously be these two sub-nfa,
				// so we must insert it before the pre_start_state's target state 
				// auto branch_state = insert_new_state(
				// 	nfa_stack.has_second_top() ? 
				// 	std::next(nfa_stack.second_top().end_state) :
				// 	states.front()
				// );
				// auto branch_state = insert_new_state_before_top_nfa();
				auto branch_state = insert_new_state(top_begin_state());

				branch_state->add_outgoing(pre_begin_edge)
					        ->add_outgoing(begin_edge);

				auto merge_state = new_state();
				pre_end_state->add_outgoing(edge::make_epsilon(merge_state));
				end_state->add_outgoing(edge::make_epsilon(merge_state));

				pre_begin_edge = edge::make_epsilon(branch_state);
				pre_end_state = merge_state;
				pre_complexity += complexity + 3;

				break;
			}
			// left parentess (, ψ( (e) ) = ψ(e) + 2
			case oper::lparen: {
				if(nfa_stack.size() < 2) return false; 
				auto [begin_edge, end_state, complexity] = nfa_stack.top();
				nfa_stack.pop();

				auto& [capture_begin_edge, dummy_state, cap_complexity] = nfa_stack.top();
				dummy_state->add_outgoing(begin_edge);
				auto capture_end_state = new_state();
				capture_begin_edge.set_capture_end(capture_end_state);
				end_state->add_outgoing(edge::make_epsilon(capture_end_state));

				dummy_state = capture_end_state;
				cap_complexity += complexity + 1;
				break;
			}
			default: {
				return false;
			}
		}
		return true;
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
		char_t c = *pos++;
		switch(c) {
		// control escapes:
		case 'f': return { {edge_category::single_char, char_t('\f')} };
		case 'n': return { {edge_category::single_char, char_t('\n')} };
		case 'r': return { {edge_category::single_char, char_t('\r')} };
		case 't': return { {edge_category::single_char, char_t('\t')} };
		case 'v': return { {edge_category::single_char, char_t('\v')} };
		case '0': return { {edge_category::single_char, char_t('\0')} };
		case 'b': return { {edge_category::single_char, char_t('\b')} }; // backspace // TODO: this works only when in bracket expression, in other situation, this is a block identify character

		case 'c': {
			if(pos != end) {
				return { {edge_category::single_char, char_t(*pos++ % 32)} };
			}else {
				// bad escape
				return { std::nullopt };
			}
		}
		case 'x': {
			if(pos != end) {
				auto val = hex_val(*pos++);
				if((pos + 1) != end) {
					return { {edge_category::single_char, char_t(val * 0x10 + hex_val(*pos++))} };
				}else {
					// actually it's a bad escape
					return { {edge_category::single_char,  char_t(val)} };
				}
			}else {	
				// it is also a bad escape
				++pos;
				return { std::nullopt };
			}
		}

		case 'd': return { {edge_category::digits    } };
		case 'D': return { {edge_category::non_digits} };
		case 's': return { {edge_category::spaces    } }; 
		case 'S': return { {edge_category::non_spaces} };
		case 'w': return { {edge_category::words     } };
		case 'W': return { {edge_category::non_words } };

		}
		// idenitity escapes
		return { {edge_category::single_char, c} };

	}

	tuple<error_category, const char_t*> parse(string_view_t s) {
		// shunting yard algorithm
		// operator priority:  *  > (concatnation) > |
		// supported operator: 
		// *,  |, (concatnation), ., 
		
		reset();
		
		if(s.empty()) return {build_result = error_category::empty_pattern, nullptr};

		bool has_potential_concat_oper = false;
		
		for(auto pos = s.begin(); pos != s.end();) {
			switch(*pos) {
			case '*':   // kleene closure
			case '+':   // positive closure, (r)+ ::= (r)(r)*
			case '?': { // optional,         (r)? ::= (r)|ε

				// *, +, ? have the highest priorities, so directly reduce it
				if(!reduce(to_oper(*pos))) return {build_result = error_category::empty_operand, pos};
				++pos;
				has_potential_concat_oper = true;
				break;
			}
			case '|': {
				// alternative / 'or' operator
				while(!oper_stack.empty() && priority(oper_stack.top()) >= priority(oper::alter)) {
					if(!reduce()) return {build_result = error_category::empty_operand, pos};
					oper_stack.pop();
				}
				oper_stack.push(oper::alter);
				++pos;
				has_potential_concat_oper = false;
				break;
			}
			case '(': {
				if(has_potential_concat_oper && !reduce_concat()) return {build_result = error_category::empty_operand, pos};
				// make_capture_group();

				++max_capture_id;
				auto dummy_state = new_state();
				edge capture_begin = edge::make_capture(max_capture_id);
				// dummy_state->add_outgoing(capture_begin, dummy_state);

				nfa_stack.emplace(capture_begin, dummy_state, 1);
				oper_stack.push(oper::lparen);
				++pos;
				has_potential_concat_oper = false;
				break;
			}
			case ')': {
				while(!oper_stack.empty() && oper_stack.top() != oper::lparen) {
					if(!reduce()) return {build_result = error_category::empty_operand, pos};
					oper_stack.pop();
				}

				if(oper_stack.empty()) return {build_result = error_category::missing_paren, pos}; // error: missing left paren '('
				else {
					// the top must be lparen '(', reduce it to build a capture
					reduce();
					oper_stack.pop();
				}
				++pos;
				has_potential_concat_oper = true;
				break;
			}
			case '[': {
				// [c...] bracket expression
				if(++pos == s.end()) return {build_result = error_category::bad_bracket_expression, pos};
				bool invert_range = false;
				if(*pos == '^') {
					invert_range = true;
					++pos;
				}
				if(auto brackets_res = parse_brackets(pos, s.end()); brackets_res.has_value()) {
					if(has_potential_concat_oper && !reduce_concat()) return {build_result = error_category::empty_operand, pos};

					if(!invert_range) reduce_brackets(brackets_res.value());
					else              reduce_brackets_invert(brackets_res.value()); 
				}else return {build_result = error_category::bad_bracket_expression, pos};
				
				has_potential_concat_oper = true;
				break;

			}
			case '{': {
				// {m}, {m,}, {m,n}  counted repetition expression
				auto braces_res = parse_braces(++pos, s.end());
				if(braces_res.kind == braces_result::error)
					return {build_result = error_category::bad_brace_expression, pos};
				if(!reduce_braces(braces_res)) 
					return {build_result = error_category::expensive_brace_expression_unroll, pos};
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
					else return {build_result = error_category::bad_escape, pos};
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
					return {build_result = error_category::empty_operand, pos};
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
				return {build_result = error_category::missing_paren, s.end()};
			}else if(!reduce()) {
				return {build_result = error_category::empty_operand, s.end()};			
			}
			oper_stack.pop();
		}

		// is the element count of nfa_stack possible to be more then 1?
		assert(nfa_stack.size() == 1);

		// insert start state
		// auto start_state = insert_new_state(states.begin());

		insert_new_state(states.begin())->add_outgoing(nfa_stack.top().begin_edge);

		final_state = nfa_stack.top().end_state;

		// assign states' id
		state_id_t id = 0;
		for(auto& s: states) s.id = id++;

		while(!nfa_stack.empty()) nfa_stack.pop();

		return {build_result = error_category::success, s.end()};
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
						edges.back() = edge::make_range({from, to}); // [p-\q]
					}else return { std::nullopt };
				default:
					// chars
					// parse_char_literally

					edges.back() = edge::make_range({from, *pos}); // [p-q]
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

			auto pre_state = insert_new_state(post_state);
			for(auto& e: edges) {
				pre_state->add_outgoing(e.set_target(post_state));
			}
			nfa_stack.emplace(edge::make_epsilon(pre_state), post_state, edges.size() + 1);
			
		}
	}

	void reduce_brackets_invert(vector<edge>& edges) {
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
			auto pre_state = insert_new_state(post_state, true); // is_conjunction = true

			for(auto& e: edges) {
				pre_state->add_outgoing(e.set_target(post_state));
			}
			nfa_stack.emplace(edge::make_epsilon(pre_state), post_state, edges.size() + 1);

		}
	}

	struct braces_result {
		enum kind_category {
			error = 0, 
			fixed, // {m} 
			left_bounded, // {m,}
			bounded, // {m, n}
		} kind;
		size_t low, high; // m, n

		static constexpr braces_result make_error() noexcept {
			return {error};
		}

		friend constexpr bool operator==(const braces_result& l, const braces_result& r) noexcept {
			if(l.kind == r.kind) {
				return l.kind == error || l.low == r.low && l.high == r.high;
			}else return false;
		} 
	};

	// counted loop 'R{n,m}' grammer
	bool reduce_braces(const braces_result& braces_res) {
		if(try_unroll_brace_expression(braces_res)) {
			return true;
		}
		// TODO: implement counted repetition loop? is it possible?
		// we probaly need to do something on the runtime machine, a 'stateful' state
		return false; 
	}

	// TODO: in the consideration of optimization, let it can create more than one copy, which allow us reuse memo. 
	// deep copy the stack top sub-nfa before itself
	subnfa copy_before(const subnfa& nfa, state_iterator_t begin_state, bool remove_capture = true) {
		// deep copy a sub-nfa before the source nfa, and promise states' relative order is not changed,
		// notice: if the source sub-nfa contains capture, 
		// at the runtime, the captured string will be reset on the next match
		// for example: (R){m}, it will only capture the last match string of R, but not m captures of each R match
		// this should be handle properly.

		const auto [begin_edge, end_state, complexity] = nfa;		
		// const auto [begin_edge, end_state, complexity] = nfa_stack.top();

		// unordered_map does not support iterator as key, so we use pointer instead 
		unordered_map<const state_iterator_t, state_iterator_t, state_iterator_hash> memo;

		// if a state is not in the memo, return itself,
		// which means if a state is not in the range of src sub-nfa, directly return the state itself, 
		// but not the dst state it corresponding to.
		auto memo_get = [&memo] (const state_iterator_t& it) {
			auto res = memo.find(it);
			return res == memo.end() ? it : res->second;
		};

		for(auto it = begin_state; it != end_state; ++it) {
			memo[it] = insert_new_state(begin_state, it->is_conjunction);
		}
		memo[end_state] = insert_new_state(begin_state, end_state->is_conjunction);

		auto copy_begin_edge = edge{begin_edge, memo_get(begin_edge.target)};
		if(remove_capture) {
			for(auto& [src, dst]: memo) {
				for(auto& e: src->edges) {
					if(e.has_capture()) dst->add_outgoing(edge{e, memo_get(e.target)}.remove_capture());
					else dst->add_outgoing(edge{e, memo_get(e.target)});
				}
			}
			if(begin_edge.has_capture()) copy_begin_edge.remove_capture();
		}else {
			// reserve the edges capture.id, but we should redirect capture.end 
			for(auto& [src, dst]: memo) {
				for(auto& e: src->edges) {
					if(e.has_capture()) dst->add_outgoing(
						edge{e, memo_get(e.target)}.set_capture_end(memo_get(e.data.capture.end))
					);
					else dst->add_outgoing(edge{e, memo_get(e.target)});
				}
			}
			if(begin_edge.has_capture()) copy_begin_edge.set_capture_end(memo_get(begin_edge.data.capture.end));
		}
		return {
			copy_begin_edge, 
			memo_get(end_state), 
			complexity
		};
	}

	bool try_unroll_brace_expression(const braces_result& braces_res) {
		// R{m}   == R...R            m times R
		// R{m,}  == R...R+           m times R
		// R{m,n} == R...R(R?)...(R?) m times R and n-m times R?, 
		// however, we use a slightly trickly way to implement but not directly unroll it

		// (R){m}  == R...(R)             m times R, but capture the last R, 
		// (R){m,} == R...(R)+            m times R, but capture the last R

		// (R){m,n} == R...(R)(R?)...(R?) m times R and n-m times R?, but capture the last R,
		// here the parentheses identify the same capture


		// the sub-nfa to copy is on the top of the stack now
		auto& [begin_edge, end_state, complexity] = nfa_stack.top();
		auto begin_state = top_begin_state();
		
		auto unroll_fixed_brace_expression = 
			[this, begin_state](size_t copy_count, bool remove_capture = true) {
 
			auto& nfa = nfa_stack.top();
			assert(copy_count >= 1);
			auto [first_begin_edge, current_end_state, _] = copy_before(nfa, begin_state, remove_capture);

			for(size_t i = 0; i < copy_count - 1; ++i) {
				auto [new_begin_edge, new_end_state, _] 
					= copy_before(nfa, begin_state, remove_capture);
				
				current_end_state->add_outgoing(new_begin_edge);
				current_end_state = new_end_state;
			}

			return subnfa{
				first_begin_edge, 
				current_end_state
				// no need to return complexity
			};

		};

		auto [kind, m, n] = braces_res;
		complexity_t new_complexity;
		
		switch(kind) {
		case braces_result::bounded: // R{m,n}
			if(m != n) {
				// new_complexity = n * complexity + n - m;
				if((new_complexity = n * (complexity + 1) - m) > max_unroll_complexity) return false;
				
				// (R){m,n} == R{m}(R){0,n-m}
				// (R){m,n} == R{m-1}(R)(R){0,n-m}
				
				// TODO: too many branches, need to be optimized
				
				if(m == 0) {
					auto post_end_state = new_state();
					end_state->add_outgoing(edge::make_epsilon(post_end_state));
					// (R){0,n} == (R){1,n}?
					if(n != 1) {
						auto [copy_begin_edge, copy_end_state, _] = unroll_fixed_brace_expression(n - 1, false);
						copy_end_state->add_outgoing(begin_edge);
						begin_edge = copy_begin_edge;
						end_state = post_end_state;
					}
					complexity = new_complexity;
					reduce(oper::optional);
				}else if(m == 1) {
					// (R){1, n}
					auto post_end_state = new_state();
					end_state->add_outgoing(edge::make_epsilon(post_end_state));
					
					auto [copy_begin_edge, copy_end_state, _] = unroll_fixed_brace_expression(n - 1, false);
					copy_end_state->add_outgoing(begin_edge);

					begin_edge = copy_begin_edge;
					end_state = post_end_state;
					complexity = new_complexity;
				}else {
					// m > 1
					auto [pre_copy_begin_edge, pre_copy_end_state, pre_copy_complexity] = unroll_fixed_brace_expression(m - 1);
// embarassing,,
					auto post_end_state = new_state();
					end_state->add_outgoing(edge::make_epsilon(post_end_state));
					
					auto [copy_begin_edge, copy_end_state, copy_complexity] = unroll_fixed_brace_expression(n - m, false);
					copy_end_state->add_outgoing(begin_edge);
					pre_copy_end_state->add_outgoing(copy_begin_edge);

					begin_edge = pre_copy_begin_edge;
					end_state = post_end_state;
					complexity = new_complexity;
				}
				break;
			} // else m == n: e{m,m} == e{m}
			[[fallthrough]];
		case braces_result::fixed: // e{m}
			if(m == 0) {
				// R{0} == ε
				// remove useless states
				// no need to reset the capture group
				states.erase(begin_state, std::next(end_state));
				nfa_stack.pop();
			}else if(m >= 2) {
				// R{1} == R, so we do nothing
				// R{m} , where m >= 2, 
				
				if((new_complexity = m * complexity) > max_unroll_complexity) return false;

				// total m times R, copy (m - 1) times
				// generates R...R, where R repeat m - 1 times 
				auto [copy_begin_edge, copy_end_state, _] = unroll_fixed_brace_expression(m - 1);
				copy_end_state->add_outgoing(begin_edge);
				
				begin_edge = copy_begin_edge;
				complexity = new_complexity;
			}
			break;
		case braces_result::left_bounded: // e{m,}
			if(m == 0) {
				// R{0,} == R*
				reduce(oper::kleene);
			}else if(m == 1){
				// R{1,} == R+
				reduce(oper::positive);
			}else {
				// R{m,} == R ... R+
				// (R){m,} == R ... (R)+
 				if((new_complexity = m * complexity + 1) > max_unroll_complexity) return false;

				auto [copy_begin_edge, copy_end_state, _] = unroll_fixed_brace_expression(m - 1);

				reduce(oper::positive);

				copy_end_state->add_outgoing(begin_edge);

				begin_edge = copy_begin_edge;
				complexity = new_complexity;
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

		typename braces_result::kind_category kind = braces_result::error;
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

	error_category get_result() const noexcept {
		return build_result;
	}

	// generate a nfa as our result
	nfa_t generate() {
		if(build_result != error_category::success) {
			return {}; // return a empty nfa
		}

		nfa_t nfa(states.size());

		auto it = states.cbegin();
		auto nfa_it = nfa.states.begin();
		while(it != states.cend()) {
			*nfa_it = it->generate();
			++it;
			++nfa_it;
		}
		nfa.final_state = final_state->id;
		nfa.max_capture_id = max_capture_id;
		return nfa;
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
	

}; // nfa_builder

template <typename CharT>
struct non_determinstic_finite_automaton {
	// output of nfa_builder, 
	// a non-determinstic-finite-automaton(NFA)


	// NFA M = (Q, Σ, δ, q0, f) 
	using char_t = CharT; // Σ
	using range_t = char_range<char_t>;

	using nfa_builder_t = nfa_builder<char_t>;

	using group_id_t = size_t;
	using state_id_t = size_t;

	struct capture_info {
		group_id_t id = 0;
		state_id_t end;
	};
	
	struct edge {

		edge_category category;
		state_id_t target;

		union edge_data {
			char_t single_char;
			range_t range;
			capture_info capture;
		} data;


		bool accept(char_t c) const noexcept{
			switch(category) {
			case edge_category::epsilon: 
				return false; 
			case edge_category::single_char: // range of one char [from]
				return c == data.single_char;
			case edge_category::range:       // range: [from-to]
				return in_range(data.range, c);
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
				return c != data.single_char;
			case edge_category::invert_range:       // [^from-to]
				return !in_range(data.range, c);
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

		bool is_epsilon() const noexcept {
			return category == edge_category::epsilon;
		}

		bool is_single_char() const noexcept{
			return category == edge_category::single_char;
		}

		bool is_range() const noexcept{
			return category == edge_category::range;
		}

		bool is_capture_begin() const noexcept{
			return category == edge_category::epsilon && data.capture.id != 0;
		}

		edge_category get_category() const noexcept{
			return category;
		}

		capture_info get_capture() const noexcept{
			return data.capture;
		}


	}; // struct edge

	struct state {
		
		vector<edge> edges;
		bool is_conjunction = false;

		edge& operator[](size_t i) {
			return edges[i];
		}
		const edge& operator[](size_t i) const{
			return edges[i];
		}
		
	};

	vector<state> states;
	state_id_t final_state = 0;
	size_t max_capture_id = 0;

	friend nfa_builder_t;

	state& operator[](state_id_t id) {
		return states[id];
	}

	const state& operator[](state_id_t id) const{
		return states[id];
	}

protected:
	
	// build it from nfa_builder
	non_determinstic_finite_automaton() noexcept = default;
	non_determinstic_finite_automaton(size_t state_count): states(state_count) {}

}; // struct non_determinstic_finite_automaton

template <typename CharT>
struct regular_expression_engine {

	using char_t = char;
	using string_view_t = basic_string_view<char_t>;
	using string_iterator_t = string_view_t::const_iterator;
	using nfa_t = non_determinstic_finite_automaton<char_t>;

	using state_id_t = typename nfa_t::state_id_t;
	using group_id_t = size_t;
	using capture_result_t = vector<string_view_t>;


	// stores the contexts of captures in running nfa
	// use during runtime
	struct state_context {

		struct capture {

			string_iterator_t begin, end;

			// bool completed = false;

			constexpr capture() noexcept = default;
			constexpr capture(string_iterator_t begin) noexcept: begin{begin}, end{begin} {}
			
			capture& reset(string_iterator_t new_begin) noexcept{
				begin = end = new_begin;
				return *this;
			}

			capture& complete(string_iterator_t pos) noexcept{
				end = std::next(pos);
				return *this;
			}

			bool try_complete(string_iterator_t pos) noexcept{
				if(end == begin) {
					 this->end = std::next(pos);
					 return true;
				}
				return false;
			}

			bool completed() const noexcept{
				return begin != end;
			}

		}; // struct capture

		
		// group_id -> captures
		unordered_map<group_id_t, capture> captures;
		bool active = false;

		state_context() = default;

		state_context& reset() {
			captures.clear();
			active = false;
			return *this;
		}

		capture& operator[](group_id_t group_id) {
			return captures[group_id];
		}
		const capture& operator[](group_id_t group_id) const{
			return captures[group_id];
		}

	}; // struct state_context

	
	const nfa_t& nfa;

protected:
	vector<state_context> state_contexts;
	unordered_multimap<state_id_t, group_id_t> capture_end_states;

public:

	regular_expression_engine(const nfa_t& nfa): nfa{nfa}, state_contexts(nfa.states.size()) {
		assert(!nfa.states.empty());
	}

	regular_expression_engine& reset() {
		for(auto& s: state_contexts) s.reset();
		state_contexts.front().active = true;
		// capture_results.clear();
		return *this;
	}

	// spread src's state_context to its target state by edges[edge_id]
	// it should support all kinds of edges, including ε edge
	void spread_context(state_context& src_context, const typename nfa_t::edge& e, const string_iterator_t& pos) {

		auto dist = e.target;
		auto& dist_context = state_contexts[dist];

		dist_context.active = true;
		if(e.is_epsilon()) {
			if(e.data.capture.id != 0) {
				// is capture begin
				for(auto [group_id, capture]: src_context.captures) {
					if(e.get_capture().id == group_id) 
						dist_context[group_id].reset(pos);
					else
						dist_context[group_id] = src_context[group_id];
				}

				// register the end state of this capture
				// TODO: should we dynamicly do it?
				// or build the map during nfa building time?
				capture_end_states.insert({dist, e.get_capture().id});
			}else {
				dist_context.captures = src_context.captures;
			}
		}else {
			// is a normal edge
			dist_context.captures = src_context.captures;
		}

		// complete all of the captures
		for(auto [it, end] = capture_end_states.equal_range(dist); it != end; ++it) { 
			// it->second: group id of being completed capture
			dist_context[it->second].try_complete(pos);
		}
	}


	void do_epsilon_closure(state_id_t state, const string_iterator_t& pos) {
		// apply ε-closure to state_contexts
		// all of the ε-closure(q) always maintains the same context? 
		// ε-closure(q) = {q} ∪ {p | p ∈ δ(q, ε) ∪ δ(δ(q, ε), ε) ∪ ...}	

		queue<state_id_t> que;
		que.push(state);

		unordered_map<state_id_t, bool> visited;

		while(!que.empty()) {
			auto current_state = que.front();
			que.pop();

			if(auto [it, inserted] = visited.try_emplace(current_state, true); inserted) {
				for(const auto& e: nfa[current_state].edges) {
					if(e.accept_epsilon() && visited.count(e.target) == 0) {
						que.push(e.target);
						// spread the state context
						spread_context(state_contexts[state], e, pos);
					}
				}
			}
		}
	}

	bool step(string_iterator_t pos) {
		// we must reversely iterate runtime states
		bool trapped = true;
		auto it = nfa.states.rbegin();
		auto context_it = state_contexts.rbegin();
		state_id_t id = nfa.states.size() - 1;
		while(it != nfa.states.rend()) {
			if(context_it->active) {
				// for each state in state_contexts
				// reset the current state
				context_it->active = false;
				if(it->is_conjunction) {
					// conjunction state, all of the edges must be accepted
					// all of the edges point to the same target state
					bool all_accepted = true;
					for(const auto& e: it->edges) {
						if(!e.accept(*pos)) {
							all_accepted = false;
							goto next_state;
						}
					}
					// all of the edges are accepted
					spread_context(*context_it, it->edges.front(), pos);
					do_epsilon_closure(it->edges.front().target, pos);
					trapped = false;
					next_state:;
				}else {
					for(const auto& e: it->edges) if(e.accept(*pos)) {
						spread_context(*context_it, e, pos);
						do_epsilon_closure(e.target, pos);
						trapped = false;
					}
				}
			}
			++it;
			++context_it;
			--id;
		}
		return !trapped;
	}

	capture_result_t match(string_iterator_t begin, string_iterator_t end){
		reset();
		string_iterator_t it = begin;	
		do_epsilon_closure(0, it);
		

		while(it != end) {
			if(!step(it++)) {
				// failed: can't match
				return {}; 
			}
		}
		// failed: can't match
		if(!state_contexts[nfa.final_state].active) return {};

		capture_result_t result(nfa.max_capture_id + 1);
		// result[0] is the whole match
		result.front() = make_string_view(begin, end);
		for(auto [group_id, capture]: state_contexts[nfa.final_state].captures) {
			if(capture.completed()) {
				result[group_id] = make_string_view(capture.begin, capture.end);
			}
		}
		return result;
	}

	capture_result_t match(string_view_t s) {
		auto it = s.begin();
		return match(it, s.end());
	}

	capture_result_t search(string_iterator_t& it, string_iterator_t end) {
		
		while(it != end) {
			auto current = it;
			auto result = match(current, end);
			if(!result.empty()) return result;
			++it;
		}
		return {};
	}
	capture_result_t search(string_view_t s) {
		auto it = s.begin();
		return search(it, s.end());
	}

	vector<capture_result_t> search_all(string_iterator_t begin, string_iterator_t end) {
		vector<capture_result_t> results;
		auto it = begin;
		while(it != end) {
			auto result = search(it, end);
			if(result.empty()) continue;
			results.push_back(result);
		}
		return results;
	}
	vector<capture_result_t> search_all(string_view_t s) {
		return search_all(s.begin(), s.end());
	}

}; // struct regular_expression_engine

} // namespace impl

template <typename CharT>
using regular_expression_engine = impl::regular_expression_engine<CharT>;


// free functions
template <typename CharT>
std::tuple<error_category, typename regular_expression_engine<CharT>::capture_result_t> match(std::basic_string_view<CharT> pattern, std::basic_string_view<CharT> target) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto result = builder.get_result(); result != error_category::success) 
		return {result, {}};
	else return {result, regular_expression_engine<CharT>{
		builder.generate()
	}.match(target)};
}

template <typename CharT>
std::tuple<error_category, typename regular_expression_engine<CharT>::capture_result_t> search(std::basic_string_view<CharT> pattern, std::basic_string_view<CharT> target) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto result = builder.get_result(); result != error_category::success) 
		return {result, {}};
	else return {result, regular_expression_engine<CharT>{
		builder.generate()
	}.search(target)};
}

template <typename CharT>
std::tuple<error_category, std::vector<typename regular_expression_engine<CharT>::capture_result_t>> search_all(std::basic_string_view<CharT> pattern, std::basic_string_view<CharT> target) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto result = builder.get_result(); result != error_category::success) 
		return {result, {}};
	else return {result, regular_expression_engine<CharT>{
		builder.generate()
	}.search_all(target)};
}

template <typename CharT>
std::tuple<error_category, impl::non_determinstic_finite_automaton<CharT>> compile(std::basic_string_view<CharT> pattern) {
	impl::nfa_builder<CharT> builder{pattern};
	return {builder.get_result(), builder.generate()};
}

} // namespace regex

} // namespace rais

int main(int argc, const char** argv) {
	using std::string;
	using std::cin;
	using namespace fmt;
	using namespace rais::regex;


	while(true) {
		
		string pattern = "";
		
		print("input a pattern:\n");
		cin >> pattern;

		print("pattern: {}\n", pattern);

		auto [result, nfa] = compile<char>(pattern);

		print("pattern result: {}\n", error_message(result));
		
		if(result != error_category::success) continue;
		regular_expression_engine<char> re{nfa};
		while(true) {
			string target;
			print("input a target string:\n");
			cin >> target;
			if(target == "~") break;
			auto result = re.match(target);
			print("target = {}, capture: {}\n", target, result);

		}
		
	}

	return 0;
}