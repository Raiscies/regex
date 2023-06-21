


/*
	Regular Expression Interpreter by Raiscies.
	
	Supported Grammer:
	concat
	select            | 
	brace             ()
	kleene closure    *
	positive closure  +
	optional          ?
	wildcard          .
	

*/

#include <map>
#include <set>
#include <stack>
#include <vector>
#include <string>
#include <limits>
#include <utility>
#include <cstddef>
// #include <variant>
#include <optional>
#include <iostream>
#include <string_view>

#include "fmt/core.h"

namespace rais {

using std::cin;
using std::map;
using std::set;
using std::pair;
using std::swap;
using std::byte;
using std::stack;
using std::size_t;
using std::string;
using std::vector;
// using std::variant;
using std::optional;
using std::in_place;
using std::basic_string;
using std::numeric_limits;
using std::basic_string_view;

// template <typename VariantT>
// struct index_of_template_args {};

// template <template <typename...> class Templ, typename... Types>
// struct index_of_template_args<Templ<Types...>> {
// 	private:
// 	template <typename TargetT, typename... Ts>
// 	struct impl {}; // empty Ts
// 	template <typename TargetT, typename T, typename... Ts>
// 	struct impl<TargetT, T, Ts...>: impl<TargetT, Ts...> {};
// 	template <typename TargetT, typename... Ts> 
// 	struct impl<TargetT, TargetT, Ts...> {
// 		static constexpr size_t result = sizeof...(Types) - sizeof...(Ts) - 1;
// 	};

// public:
// 	template <typename T>
// 	static constexpr size_t index_of = impl<T, Types...>::result;
// };

template <typename CharT>
struct non_determinstic_automaton {
	// a non-determinstic-automaton


	// NFA M = (Q, Σ, δ, q0, F) 
	using char_t = CharT; // Σ
	using string_view_t = basic_string_view<char_t>;

	using state_t = size_t;

	using state_set_t = set<state_t>; // type of Q or subset of Q
	
	// struct single_range {
	// 	using limits = numeric_limits<char_t>;

	// 	char_t from, to;
	// 	bool invert_range;
	// 	// if not invert_range : accept if c ∈ [from, to]
	// 	// else                : accept if c ∉ [from, to]
	// 	single_range(char_t c, bool invert_range_ = false) noexcept: from{c}, to{c}, invert_range{invert_range_} {}
	// 	single_range(char_t from_, char_t to_, bool invert_range_ = false) noexcept: from{from_}, to{to_}, invert_range{invert_range_} {} 

	// 	bool accept(char_t c) const noexcept{
	// 		return (from <= c && c <= to) ^ invert_range;
	// 	}

	// 	single_range& invert() const noexcept{
	// 		invert_range = !invert_range;
	// 		return *this;
	// 	}
	// };
	// struct epsilon {}; // ε

	struct edge {

		char_t from, to;
		enum /*class*/ range_category: char {
			epsilon = 0,     // empty edge
			single_char = 1, // range of one char [from]
			range       = 2, // range: [from-to]
			spaces      = 3, // space chars: [\f\n\r\t\v]
			words       = 4, // identifier chars(words): [0-9a-zA-Z_]
			digits      = 5, // digit chars: [0-9]
			newlines    = 6, // [\n\r](currently unused)
			all         = 7, // any chars

			conjunction_range = 8, // a flag to point out that the start state of this edge requires all of the edge it comes from is accepted (conjunction)
			
			// invert ranges 
			invert_single_char = -single_char,  // [^c]
			invert_range       = -range,        // [^from-to]
			non_spaces         = -spaces,       // [^\f\n\r\t\v]
			non_words          = -words,        // [^0-9a-zA-Z_]
			non_digits         = -digits,       // [^0-9]

			non_newlines       = -newlines,     // [^\n\r] (wildcard)

			none               = -all           // nothing could be accepted

			// invert_single_char = single_char ^ 0b0111'1111, // [^c]
			// invert_range       = range       ^ 0b0111'1111, // [^from-to]
			// non_spaces         = spaces      ^ 0b0111'1111, // [^\f\n\r\t\v]
			// non_words          = words       ^ 0b0111'1111, // [^0-9a-zA-Z_]
			// non_digits         = digits      ^ 0b0111'1111, // [^0-9]

			// non_newlines       = newlines    ^ 0b0111'1111, // [^\n\r] (wildcard)

			// none               = all         ^ 0b0111'1111  // nothing could be accepted


		};
		// bool is_conjunction_range: 1;  // this edge is a part of conjunction_range
		range_category category;


		// vector<stingle_range>: range is accepted iff all of the single_range is accepted(conjunction)
		// variant<std::monostate, epsilon, char_t, single_range, vector<single_range>> range;
		// vector<single_range> range; // conjunction_range
		state_t target_state = -1;

		// bool invert_range = false; // if it is true, then accept any chars except of the range


		// construct a range with {c}
		edge(state_t target = -1) noexcept: category{range_category::epsilon}, target_state{target} {} // an empty(epsilon) edge
		edge(range_category category_, state_t target = -1) noexcept: category{category_}, target_state{target} {}
		edge(char_t c, bool invert_range_ = false, state_t target = -1) noexcept: category{invert_range_ ? range_category::invert_single_char : range_category::single_char}, from{c}, target_state{target} {}
		edge(char_t from_, char_t to_, bool invert_range_ = false, state_t target = -1) noexcept: category{invert_range_ ? range_category::invert_range : range_category::range}, from{from_}, to{to_}, target_state{target} {}
		// edge(char_t c, bool invert_range_ = false, state_t target = -1) noexcept: range{{c, invert_range_}}, target_state{target} {}

		// // // construct a range with [from, to]
		// edge(char_t from, char_t to, bool invert_range_ = false, state_t target = -1) noexcept: range{{from, to, invert_range_}}, target_state{target} {}
		// edge(single_range sr, state_t target = -1) noexcept: range{sr}, target_state{target} {}

		// // // construct a conjunction range
		// edge(vector<single_range>&& range_, state_t target = -1) noexcept: range{std::move(range_)}, target_state{target} {}
		// edge(const vector<single_range>& range_, state_t target = -1) noexcept: range{range_}, target_state{target} {}
		

		static constexpr bool in_range(char_t a, char_t b, char_t x) noexcept{ return a <= x && x <= b; }
		bool accept(char_t c) const noexcept{
			switch(category) {
			case range_category::epsilon: 
				return false;
			case range_category::single_char: // range of one char [from]
				return c == from;
			case range_category::range:       // range: [from-to]
				return in_range(from, to, c);
			case range_category::spaces:      // space chars: [\t\n\v\f\r] == [\x09-\x0d]
				return in_range('\x09', '\x0d', c);
			case range_category::words:       // identifier chars(words): [0-9a-zA-Z_]
				return in_range('0', '9', c) || 
				       in_range('a', 'z', c) || 
				       in_range('A', 'Z', c) || 
				       (c == '_');
			case range_category::digits:      // digit chars: [0-9]
				return in_range('0', '9', c);
			case range_category::newlines:
				return c == '\n' || c == '\r';
			case range_category::all:
				return true;
			// invert ranges 
			case range_category::non_newlines:    // [^\n\r]
				return c != '\n' && c != '\r';
			case range_category::invert_single_char: // [^c]
				return c != from;
			case range_category::invert_range:       // [^from-to]
				return !in_range(from, to, c);
			case range_category::non_spaces:      // [^\t\n\v\f\r]
				return !in_range('\x09', '\x0d', c);
			case range_category::non_words:       // [^0-9a-zA-Z_]
				return not( 
					in_range('0', '9', c) || 
			    	in_range('a', 'z', c) || 
			    	in_range('A', 'Z', c) || 
			    	(c == '_'));
			case range_category::non_digits:      // [^0-9]
				return !in_range('0', '9', c);
			case range_category::none:
				return false;
			default:
				return false;
			}
			// if(range.empty()) return false; 
			// for(const auto& r: range) {
			// 	if(!r.accept(c)) return false;
			// }
			// return true;
			// using types = index_of_template_args<decltype(range)>;
		// 	switch(range.index()) {
		// 	case types::template index_of<epsilon>: // epsilon 
		// 		return false; // assumption was broken

		// 	case types::template index_of<char_t>: // single char
		// 		return (c == std::get<char_t>(range)) ^ invert_range;

		// 	case types::template index_of<single_range>: // single range
		// 		return std::get<single_range>(range).accept(c) ^ invert_range;

		// 	case types::template index_of<vector<single_range>>:	// conjunction range
		// 		if(!invert_range) {
		// 			for(const auto& r: std::get<vector<single_range>>(range)) if(r.accept(c)) return true;
		// 			return false;
		// 		}else {
		// 			for(const auto& r: std::get<vector<single_range>>(range)) if(r.accept(c)) return false;
		// 			return true;
		// 		}
		// 	default:
		// 		return false;
		// }
	}
	bool accept_epsilon() const noexcept{
		return category == range_category::epsilon;
	}
	// bool is_conjunction() const noexcept{
	// 	return is_conjunction_range;
	// }

	edge& set_target(state_t index) noexcept{
		target_state = index;
		return *this;
	}

	edge& set_range(char_t from_, char_t to_, bool invert_range_ = false) noexcept{
		from = from_;
		to = to_;
		category = invert_range_ ? range_category::invert_range : range_category::range;
		return *this;
	}
	edge& set_range(char_t c, bool invert_range_ = false) noexcept{
		from = c;
		category = invert_range_ ? range_category::invert_single_char : range_category::single_char;
		return *this;
	}
	edge& set_range(range_category category_) noexcept{
		category = category_;
		return *this;
	}


	edge& invert() noexcept{
		category = range_category(-category);
		return *this;	
	}
	bool is_single_char() const noexcept{
		return category == range_category::single_char;
	}
	bool is_conjunction_range() const noexcept{
		return category == range_category::conjunction_range;
	}
}; 

	// δ: Q * (Σ ∪ {ε}) -> 2^Q
struct transform_t {

	// accept (q, {c-spaces}) -> {q-spaces}
	vector<vector<edge>> m;

	state_set_t& do_epsilon_closure(state_set_t& current_states) const{
			// do ε-closure(current_states) and assign to itself
		state_set_t current_appended_states = current_states, 
		next_appended_states;
		while(true) {
			for(auto q: current_appended_states) {
				for(const auto& r: m[q]) {
					if(r.accept_epsilon() && current_states.count(r.target_state) == 0) {
						next_appended_states.insert(r.target_state);
					}
				}
			}
			if(next_appended_states.empty()) return current_states;

			current_states.insert(next_appended_states.begin(), next_appended_states.end());
			current_appended_states = std::move(next_appended_states);
			next_appended_states.clear();
		}
	}

	state_set_t operator()(const state_set_t& current_states, char_t c) const{
			// assume ε-closure(current_states) == current_states

		if(current_states.empty()) return {};
		state_set_t new_states;

		for(auto q: current_states) {
			// for each protential current state
			if(m[q].empty()) continue;
			else if(m[q][0].is_conjunction_range()) {
				// this state and its edges are conjunction
				// c is accepted only when all of the edges are accepted 
				for(auto it = ++m[q].cbegin(); it != m[q].cend(); ++it)
					if(!it->accept(c)) goto next_state;
				new_states.insert(m[q][0].target_state);
				next_state:;
			}else {
				for(const auto& r: m[q]) {
					// for each range
					if(r.accept(c)) new_states.insert(r.target_state);
				}
			}
		}
		return do_epsilon_closure(new_states);
	}

};

	using final_state_set_t = state_set_t; // F: is a subset of Q

private:
	state_t max_state_index = 0;

public:
	// static constexpr state_t trap_state = state_t(-1);

	transform_t delta;
	final_state_set_t F;

	non_determinstic_automaton() {
		new_state();	
	}

	void reset() {
		delta.m.clear();
		F.clear();
		max_state_index = 0;
		delta.m.emplace_back();
	}

	state_t new_state() {
		delta.m.emplace_back();
		return ++max_state_index;
	}

	void mark_final_state(state_t index) {
		F.insert(index);
	}

	// bool bind_transform(state_t index, state_t target_index, char_t begin_char, char_t end_char) {
	// 	if(index > max_state_index or target_index > max_state_index) return false;
	// 	// assume begin_char <= end_char

	// 	delta.m[index].emplace_back(begin_char, end_char, target_index);
	// 	return true;
	// }
	// bool bind_transform(state_t index, state_t target_index, char_t begin_char) {
	// 	return bind_transform(begin_char, begin_char);
	// }

	bool bind_transform(state_t index, state_t target_index, const edge& e) {
		if(index > max_state_index or target_index > max_state_index) return false;

		delta.m[index].push_back(e.set_target(target_index)); // reset reset
		return true;
	}
	bool bind_transform(state_t index, const edge& e) {
		if(index > max_state_index) return false;

		delta.m[index].push_back(e);
		return true;
	}
	bool bind_empty_transform(state_t index, state_t target_index) {
		if(index > max_state_index or target_index > max_state_index) return false;
		delta.m[index].emplace_back(target_index);
		return true;
	}

	bool execute(string_view_t target, state_set_t start_states = {0}) const{
		if(start_states.empty()) return false;

		state_set_t current_states = std::move(delta.do_epsilon_closure(start_states));
		for(auto c: target) {
			auto new_states = delta(current_states, c);
			if(new_states.empty()) return false; // this nfa does not accept target string
			current_states = std::move(new_states);
		}
		// check if (current_states ∪ F) != Φ
		for(auto q: current_states) {
			if(F.count(q) != 0) return true; // target was accepted
		}
		return false; // target is unacceptable

	}

	state_set_t single_execute(char_t c, state_set_t start_states) const{

		return delta(delta.do_epsilon_closure(start_states), c);
	}
};

template <typename CharT>
using nfa = non_determinstic_automaton<CharT>;

template <typename CharT>
struct regular_expression {
	using char_t = CharT;
	using string_t = basic_string<char_t>;
	using string_view_t = basic_string_view<char_t>;

	using nfa_t = nfa<char_t>;
	using edge = typename nfa_t::edge;
	using state_t = typename nfa_t::state_t;
	// using single_range = typename nfa_t::single_range;
	// using epsilon = typename nfa_t::epsilon;

	//parsing output: NFA M = (Q, Σ, δ, q0, F) 
	nfa_t output;

	regular_expression(string_view_t pattern) {
		parse(pattern);
	}
	regular_expression() noexcept = default;

	enum error_category {
		success = 0,
		empty_operand, 
		bad_escape, 
		missing_brace,
		bad_breaket_expression
	};

	enum class oper {
		// enum value represents the priority of the operators
		kleene,     // *
		positive,   // +
		optional,   // ?
		concat,     // (concatnation)
		select,     // |
		lbrace,     // (
		rbrace,     // ) the priority of right-brace is meanless
		wildcard,   // . the priority of wildcard is meanless
		breaket,       // [chars...]
		breaket_invert // [^chars...]
	};

	static constexpr int priority(oper op) noexcept{
		switch(op) {
		case oper::kleene   : 
		case oper::positive :
		case oper::optional : 
		case oper::breaket  :
		case oper::breaket_invert: 
			return 0;
		case oper::concat   : return -1;
		case oper::select   : return -2;
		case oper::lbrace   : return -3;
		default: return -114514;
		}
	}
	static constexpr oper to_oper(char_t c) noexcept{
		switch(c) {
		case '*': return oper::kleene;
		case '+': return oper::positive;
		case '?': return oper::optional;
		case '|': return oper::select;
		case '(': return oper::lbrace;
		case ')': return oper::rbrace;
		case '.': return oper::wildcard;
		default: return oper(-1);
		}
	}

	pair<error_category, const char_t*> parse(string_view_t s) {
		// RE don't need to tokenize because each of the char (except of escape char sequences) is a token
		// // using table driven recursive descent predictted algorithm
		
		// shunting yard algorithm
		// operator priority:  *  > (concatnation) > |
		// supported operator: 
		// *,  |, (concatnation), ., 
		
		output.reset();
		
		if(s.empty()) return {success, nullptr};
		

		stack<oper> oper_stack;
		stack<pair<edge, state_t>> output_stack;
		bool has_potential_concat_oper = false;
		for(auto pos = s.begin(); pos != s.end();) {
			switch(*pos) {
			case '*': // kleene closure
			case '+': // positive closure,       (r)+ ::= (r)(r)*
			case '?': // optional/question mark, (r)? ::= (r)|ε

				// *, +, ? have the highest priority
				if(!reduce(output_stack, to_oper(*pos))) {
					return {empty_operand, pos};
				}
				++pos;
				has_potential_concat_oper = true;
				break;

			case '|':
				// select/'or' operator
				while(!oper_stack.empty() && priority(oper_stack.top()) >= priority(oper::select)) {
					if(!reduce(output_stack, oper_stack.top())) {
						return {empty_operand, pos};
					}
					oper_stack.pop();
				}
				oper_stack.push(oper::select);

				++pos;
				has_potential_concat_oper = false;
				break;

			case '(':
				if(has_potential_concat_oper && !insert_concat_oper(output_stack, oper_stack)) {
					return {empty_operand, pos};
				}
				oper_stack.push(oper::lbrace);
				++pos;
				has_potential_concat_oper = false;
				break;
			case ')':
				while(!oper_stack.empty() && oper_stack.top() != oper::lbrace) {
					if(!reduce(output_stack, oper_stack.top())) {
						return {empty_operand, pos};
					}
					oper_stack.pop();
				}
				if(oper_stack.empty()) {
					// error: missing left brace '('
					return {missing_brace, pos};
				}
				oper_stack.pop(); // pop out left brace (
				++pos;
				has_potential_concat_oper = true;
				break;
			case '[': {
				// [c...] breaket expression
				if(++pos == s.end()) return {bad_breaket_expression, pos};
				bool invert_range = false;
				if(*pos == '^') {
					invert_range = true;
					++pos;
				}
				if(auto breaket_res = parse_breaket(pos, s.end()); breaket_res.has_value()) {
					if(!invert_range) reduce_breaket(output_stack, breaket_res.value());
					else              reduce_breaket_invert(output_stack, breaket_res.value()); 
				}else return {bad_breaket_expression, pos};
				
				has_potential_concat_oper = true;
				break;
			}
			default: {
				// is character(s)/wildcard
				edge e;
				state_t q = output.new_state();
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
					e = { edge::range_category::non_newlines };
					++pos;
					break;
				default:
					e = {*pos};
					++pos;
				}
				
				e.set_target(q);
				if(has_potential_concat_oper && !insert_concat_oper(output_stack, oper_stack)) {
					return {empty_operand, pos};
				}
				// push char
				output_stack.emplace(std::move(e), q);
				
				has_potential_concat_oper = true;
				break;
			} // default
			} // switch
		}
		// clear stacks
		while(!oper_stack.empty()) {
			if(oper_stack.top() == oper::lbrace) {
				// missing right brace ')'
				return {missing_brace, s.end()};
			}else if(!reduce(output_stack, oper_stack.top())) {
				
				return {empty_operand, s.end()};			
			}
			oper_stack.pop();
		}
		output.bind_transform(0, output_stack.top().first);
		output.mark_final_state(output_stack.top().second);
		return {success, s.end()};
	}

	bool insert_concat_oper(stack<pair<edge, state_t>>& output_stack, stack<oper>& oper_stack) {
		// insert a implicit concat operator
		while(!oper_stack.empty() && priority(oper_stack.top()) >= priority(oper::concat)) {
			if(!reduce(output_stack, oper_stack.top())) return false;
			oper_stack.pop();
		}
		// empty oper_stack or oper_stack.top() < concat
		oper_stack.push(oper::concat);
		return true;
	}

	optional<edge> lex_escape(typename string_view_t::const_iterator& pos, const typename string_view_t::const_iterator& end) {

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
		case 'f': return {'\f'};
		case 'n': return {'\n'};
		case 'r': return {'\r'};
		case 't': return {'\t'};
		case 'v': return {'\v'};
		case '0': return {'\0'};
		case 'b': return {'\b'}; // backspace // TODO: this works only when in breaket expression.
		case 'c': {
			if(pos != end) {
				return { char_t(*pos++ % 32) };
			}else {
				// bad escape
				return {};
			}
		}
		case 'x': {
			if(pos != end) {
				auto val = hex_val(*pos++);
				if((pos + 1) != end) {
					return { char_t(val * 0x10 + hex_val(*pos++)) };
				}else {
					// actually it's a bad escape
					return { char_t(val) };
				}
			}else {	
				// it is also a bad escape
				++pos;
				return {};
			}
		}

		case 'd': return { edge::range_category::digits     };
		case 'D': return { edge::range_category::non_digits };
		case 's': return { edge::range_category::spaces     }; 
		case 'S': return { edge::range_category::non_spaces };
		case 'w': return { edge::range_category::words      };
		case 'W': return { edge::range_category::non_words  };

		}
		// idenitity escapes
		return { *pos };

	}

	bool reduce(stack<pair<edge, state_t>>& output_stack, oper op, const pair<edge, state_t>& current_edge_state) {
		switch(op) {
		case oper::kleene: {  // *
			// unary operator
			auto& [e, q] = current_edge_state;    
			output.bind_transform(q, e);     // q -e->...> q
			edge new_e {q};                  // new_e = -ε->
			output_stack.emplace(new_e, q);  // -new_e-> q
			break;
		}
		case oper::positive: { // +
			// unary operator
			auto& [e, q] = current_edge_state;
			output.bind_transform(q, e);    // -e->...> q -e->...> q
			output_stack.emplace(e, q);     // -e->...> q
			break;
		} 
		case oper::optional: { // ?
			// unary operator
			auto& [e, q] = current_edge_state;
			state_t new_q = output.new_state();
			output.bind_transform(new_q, e);
			output.bind_empty_transform(new_q, q);
			edge new_e = {new_q};
			output_stack.emplace(new_e, q);
			break;
		}
		case oper::concat: {  // (concatnation)
			if(output_stack.empty()) return false;
			// binary operator
			auto [e0, q0] = output_stack.top();
			auto& [e1, q1] = current_edge_state;
			output_stack.pop();
			output.bind_transform(q0, e1);   // q0 -e1->...> q1
			output_stack.emplace(e0, q1);    // -e0->...> q0 -e1->...> q1
			break;
		}
		case oper::select: { // |
			if(output_stack.empty()) return false;
			// binary operator
			auto [e0, q0] = output_stack.top();
			auto& [e1, q1] = current_edge_state;
			output_stack.pop();
			state_t new_q = output.new_state();
			output.bind_empty_transform(q0, new_q);  // q0 -ε-> new_q
			output.bind_empty_transform(q1, new_q);  // q1 -ε-> new_q
			state_t new_q2 = output.new_state();     // create new_q
			output.bind_transform(new_q2, e0);       // new_q2 -e0->...> q0
			output.bind_transform(new_q2, e1);       // new_q2 -e1->...> q1
			edge new_e = {new_q2};                   // new_e = -ε->
			output_stack.emplace(new_e, new_q);      // -new_e-> new_q2 -{-e0->...> q0, -e1->...> q1}-> new_q
			break;
		}
		default: {
			// unknown operators
		}
		}
		return true;
	}
	bool reduce(stack<pair<edge, state_t>>& output_stack, oper op) {
		if(output_stack.empty()) return false;
		auto top = output_stack.top();
		output_stack.pop();
		return reduce(output_stack, op, top);
	}
	void reduce_breaket(stack<pair<edge, state_t>>& output_stack, vector<edge>& edges) {
		if(edges.empty()) {
			// []
			state_t new_q = output.new_state();
			// -x-> new_q
			// always not accept
			output_stack.emplace(edge{edge::range_category::none, new_q}, new_q);
		}
		// [r1...rn]
		state_t new_q1 = output.new_state(), 
		        new_q2 = output.new_state();
		edge new_e = {new_q1}; // new_e: -ε-> new_q1
		// -ε-> new_q1 -{e1, e2, ...en}-> new_q2
		for(auto& e: edges) 
			output.bind_transform(new_q1, e.set_target(new_q2));

		output_stack.emplace(new_e, new_q2);
	}
	void reduce_breaket_invert(stack<pair<edge, state_t>>& output_stack, vector<edge>& edges) {
		if(edges.empty()) {
			// [^]
			state_t new_q = output.new_state();
			// ---> new_q
			// always accept
			output_stack.emplace(edge{edge::range_category::all, new_q}, new_q);
		}else if(edges.size() == 1) {
			// [^r]
			state_t new_q = output.new_state();
			// -^e-> new_q
			output_stack.emplace(edges[0].invert().set_target(new_q), new_q);
		}else {
			// [^r1...rn]
			state_t new_q1 = output.new_state(), 
			        new_q2 = output.new_state();
			edge new_e = {new_q1}; // new_e: -ε-> new_q1
			output.bind_transform(new_q1, edge{edge::range_category::conjunction_range, new_q2});
			// -ε-> new_q1 -{conjunction_flag, ^e1, ^e2, ...^en}-> new_q2
			for(auto& e: edges) 
				output.bind_transform(new_q1, e.invert().set_target(new_q2));

			output_stack.emplace(new_e, new_q2);

		}

	}

	optional<vector<edge>> parse_breaket(typename string_view_t::const_iterator& pos, const typename string_view_t::const_iterator& end) {
		// assume pos is pointing at the first char after the left square breaket '['

		// bool invert_range = false;
		// if(*pos == '^') {
		// 	invert_range = true;
		// 	++pos;
		// }
		// edge e{vector<edge::single_range>{}};
		vector<edge> edges;
		// bool dash_is_literal = true;
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
						edges.emplace_back(lex_res.value());
					}else return {};
					state = parse_char;
					break;
				case '-':
					if(state == parse_char_literally) {
						edges.emplace_back('-');
						state = parse_char;
					}else {
						if(!edges.back().is_single_char()) return {}; // bad char range like [\w-...]
						state = parse_range;
					}
					++pos;
					break;
				default:
					// chars
					edges.emplace_back(*pos++);
					state = parse_char;
				}
			}else {
				// state == parse_range
				switch(*pos) {
				case '\\': 
					if(auto lex_res = lex_escape(++pos, end); lex_res.has_value()) {
						if(!lex_res.value().is_single_char()) {
							return {}; // bad char range like: [c-\w]
						}
						edges.back().set_range(edges.back().from, lex_res.value().from); // [p-\q]
					}else return {};
				default:
					// chars
					// parse_char_literally
					edges.back().set_range(edges.back().from, *pos); // [p-q]
					++pos;
				}
				state = parse_char_literally;
			}
		}
		// if(invert_range) {
		// 	for(auto& e: edges) e.invert();
		// }
		if(pos == end) {
			return {};
		}
		++pos;
		return edges;
	}

	// state_t build_kleene_closure(state_t start, state_t end, edge e) {
	// 	output.bind_empty_transform(start, end);
	// 	output.bind_transform(end, end, e);
	// 	return end;
	// }

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

	// static optional<edge> merge_range(const edge& e1, const edge& e2) {

	// }

}; // struct regular_expression

} // namespace rais

int main(int argc, const char** argv) {
	if(argc <= 1) return 0;
	using namespace rais;

	fmt::print("pattern: {}\n", argv[1]);
	regular_expression<char> re;
	auto [parse_result, pos] = re.parse(argv[1]);
	fmt::print("pattern result: {}\n", parse_result);
	while(true) {
		string target;
		fmt::print("input a target string:\n");
		cin >> target;
		fmt::print("target = {}, result: {}\n", target, re.output.execute(target));
	}
	fmt::print("passed.\n");

	return 0;
}