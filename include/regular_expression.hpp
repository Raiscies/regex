#pragma once

/*
	Regular Expression Interpreter by Raiscies.
	
	Supported Grammer:
	concat
	alternative       | 
	marking grouping   ()
	non-marking grouping (?:)
	kleene closure    *
	positive closure  +
	optional          ?
	wildcard          .
	brackets          [...], [^...]
	braces            {m} {m,} {m,n}

	TODO: 
	1. true capture selection of alternative operator
	2. assertion:
		2.1 zero-width positive/negative lookahead
		2.2 word/non-word boundary
		2.3 line begin/end boundary
*/

#include <list>
#include <stack>
#include <queue>
#include <vector>
#include <string>
#include <limits>
#include <cstddef>
#include <cassert>
#include <utility>
#include <iterator>
#include <optional>
#include <concepts>
#include <algorithm>
#include <functional>
#include <string_view>
#include <type_traits>
#include <unordered_set>
#include <unordered_map>

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
	expensive_brace_expression_unroll, 
	unsupported_features
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
	case error_category::unsupported_features:   return "unsupported features";
	}
	return "";
}

namespace impl {
	
// functions
using std::copy;
using std::swap;
using std::forward;
using std::as_const;

// classes / aliases
using std::pair;
using std::list;
using std::tuple;
using std::queue;
using std::stack;
using std::size_t;
using std::string;
using std::vector;
using std::optional;
using std::remove_cv_t;
using std::string_view;
using std::basic_string;
using std::unordered_set;
using std::unordered_map;
using std::numeric_limits;
using std::basic_string_view;
using std::underlying_type_t;
using std::remove_reference_t;

// concepts
using std::same_as;
using std::convertible_to;
using std::constructible_from;
using std::default_initializable;

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
constexpr bool in_range(const char_range<CharT>& r, CharT x) noexcept{ return r.is_member(x); }

template <typename CharT>
constexpr int hex_val(CharT x) noexcept{
	if('0' <= x && x <= '9') {
		return x - '0';
	}else if('a' <= x && x <= 'f') {
		return (x - 'a') + 10;
	}else {
		// 'A' <= x && x <= 'F'
		return (x - 'A') + 10;
	}
}
	
enum class oper {
	// enum value represents the priority of the operators
	bad_oper = 0b0000'0000,
	kleene,                      // *
	positive,                    // +
	optional,                    // ?
	concat,                      // (concatnation)
	alter,                       // |
	wildcard,                    // . 
	brackets,                    // [chars...]
	brackets_invert,             // [^chars...]
	braces,                      // {m}, {m,}, {m,n}
	rparen,                      // ) 


	// for quickly testing stack's left parentheis
	lparen = 0b1000'0000,        // (
	lparen_non_marking,          // (?:
	lparen_positive_lookahead,   // (?= 
	lparen_negative_lookahead    // (?!
	
};

enum edge_category: unsigned char {
	single_char = 1, // range of one char [from]
	range,           // range: [from-to]
	spaces,          // space chars: [\f\n\r\t\v]
	words,           // identifier chars(words): [0-9a-zA-Z_]
	digits,          // digit chars: [0-9]
	newlines,        // [\n\r](currently unused)
	all,             // any chars
	
	// inverted ranges 

	invert = 0b1000'0000, // inverted categories bitmask
	invert_single_char = invert | single_char, // [^c]
	invert_range       = invert | range,       // [^from-to]
	non_spaces         = invert | spaces,      // [^\f\n\r\t\v]
	non_words          = invert | words,       // [^0-9a-zA-Z_]
	non_digits         = invert | digits,      // [^0-9]
	non_newlines       = invert | newlines,    // [^\n\r] (wildcard)
	none               = invert | all,         // nothing could be accepted

	
	// all of the following categories are empty edges 
	epsilon = 0b0100'0000,

	// capture group begin
	capture_begin, 
	branch_end, 

	// assertions
	assertion_mask = epsilon | 0b0010'0000,

	assert_line_begin,         // ^ 
	assert_line_end,           // $
	
	assert_word_boundary,      // \b
	assert_non_word_boundary,  // \B

	// probaly would never be implemented :(
	assert_positive_lookahead, // (?= ) 
	assert_negative_lookahead  // (?! ) 
};

enum class state_flag: unsigned char {
	none              = 0b0000'0000,
	alternative_begin = 0b0000'0001,
	conjunction_begin = 0b0000'0010, 
	loopback_end      = 0b0000'0100
};

constexpr state_flag operator~(const state_flag& flag) noexcept{
	using underlying_t = underlying_type_t<state_flag>;
	return static_cast<state_flag>(
		~static_cast<underlying_t>(flag) 
	);
}
constexpr state_flag operator|(const state_flag& lhs, const state_flag& rhs) noexcept{
	using underlying_t = underlying_type_t<state_flag>;
	return static_cast<state_flag>(
		static_cast<underlying_t>(lhs) | 
		static_cast<underlying_t>(rhs)
	);
}
constexpr state_flag operator&(const state_flag& lhs, const state_flag& rhs) noexcept{
	using underlying_t = underlying_type_t<state_flag>;
	return static_cast<state_flag>(
		static_cast<underlying_t>(lhs) & 
		static_cast<underlying_t>(rhs)
	);
}
constexpr state_flag operator^(const state_flag& lhs, const state_flag& rhs) noexcept{
	using underlying_t = underlying_type_t<state_flag>;
	return static_cast<state_flag>(
		static_cast<underlying_t>(lhs) ^ 
		static_cast<underlying_t>(rhs)
	);
}
constexpr state_flag& operator|=(state_flag& lhs, const state_flag& rhs) noexcept{
	return lhs = lhs | rhs;
}
constexpr state_flag& operator&=(state_flag& lhs, const state_flag& rhs) noexcept{
	return lhs = lhs & rhs;
}
constexpr state_flag& operator^=(state_flag& lhs, const state_flag& rhs) noexcept{
	return lhs = lhs ^ rhs;
}

template <typename ResultViewT>
constexpr bool operator!(const state_flag& flag) noexcept{
	return static_cast<underlying_type_t<state_flag>>(flag) == 0;
}

template <typename CharT>
struct non_determinstic_finite_automaton;

template <typename CharT> 
struct nfa_builder {
	// a factory of non-determinstic-finite-automaton
	// NFA M = (Q, Σ, δ, q0, f) 
	
	/*	sub expression(e) complexity(ψ) algorithm:

		TODO: out of dated, needs update

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

	using pattern_view_t = basic_string_view<char_t>;
	using pattern_iterator_t = typename pattern_view_t::iterator;

	using nfa_t = non_determinstic_finite_automaton<char_t>;

	// indicate a sub nfa's complexity
	using complexity_t = size_t;
	
	using state_id_t = size_t;
	
	static constexpr complexity_t default_unroll_complexity = 2000;
	complexity_t max_unroll_complexity = default_unroll_complexity;

	constexpr nfa_builder() = default;

	nfa_builder(pattern_view_t s) {
		parse(s);
	}
	
	struct edge;
	
	// internal representation(IR) of NFA state
	struct state {
		
		state_flag flag;

		// out-going edges
		vector<edge> edges;

		// this will be assigned after parsing
		state_id_t id;
		
		state* add_outgoing(const edge& e) {
			edges.push_back(e);
			return this;
		}
		
		typename nfa_t::state generate() const{
			typename nfa_t::state s{flag};
			for(const auto& e: edges) {
				s.edges.push_back(e.generate());
			}
			return s;
		}
	}; // state

	list<state> states;
	
	using state_iterator_t = typename list<state>::iterator;
	using const_state_iterator_t = typename list<state>::const_iterator;

	// iterator is not hashable by default,
	// so implementing a hash function for state_iterator_t is necessary
	struct state_iterator_hash {
		// this function requires it is dereferenceable	
		constexpr size_t operator()(const state_iterator_t& it) const noexcept{
			return std::hash<const state*>()(&*it);
		}
	};

	state_iterator_t final_state;
	size_t max_capture_id = 0;

	// internal representation(IR) for NFA edge
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
			// active when category == capture_begin
			capture_info capture;
			// active when category == branch_end
			size_t branch_id;

			constexpr edge_data(): capture{} {}
			constexpr edge_data(char_t c): single_char{c} {}
			constexpr edge_data(range_t r): range{r} {}
			constexpr edge_data(capture_info cap): capture{cap} {}
			constexpr edge_data(size_t b): branch_id{b} {}
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
			return {edge_category::epsilon, {}, target};
		}

		static constexpr edge make_single_char(char_t c, state_iterator_t target = {}) noexcept{
			return {edge_category::single_char, c, target};
		}

		static constexpr edge make_range(range_t range, state_iterator_t target = {}) noexcept{
			return {edge_category::range, range, target};
		}

		static constexpr edge make_capture(size_t capture_group_id, state_iterator_t capture_end = {}, state_iterator_t target = {}) noexcept{
			return {edge_category::capture_begin, capture_info{capture_group_id, capture_end}, target};
		}

		static constexpr edge make_branch_end(size_t branch_id, state_iterator_t target = {}) noexcept{
			return {edge_category::branch_end, edge_data{branch_id}, target};
		}

		edge& set_target(state_iterator_t target) noexcept{
			this->target = target;
			return *this;
		}

		edge& invert() noexcept{
			// invert the highest bit of category
			category = edge_category(static_cast<underlying_type_t<edge_category>>(category) ^ edge_category::invert); 
			return *this;
		}

		bool has_capture() const noexcept{
			return category == edge_category::capture_begin;
		}

		edge& set_capture_end(state_iterator_t capture_end) {
			assert(has_capture());
			data.capture.end = capture_end;
			return *this;
		}
		edge& remove_capture() noexcept{
			assert(has_capture());
			// data.capture.id = 0;
			category = edge_category::epsilon;	
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
					break;
				case edge_category::range: 
				case edge_category::invert_range:
					res.data.range = data.range;
					break;
				case edge_category::capture_begin:
					res.data.capture = typename nfa_t::capture_info {
						data.capture.id, 
						data.capture.end->id
					};
					break;
				case edge_category::branch_end:
					res.data.branch_id = data.branch_id;
					break;
				default:
					// whatever
					break;
			}
			return res;
		}

	}; // edge

	struct subnfa {
		edge begin_edge;

		state_iterator_t end_state;   // the state with the highest index of the sub-nfa

		complexity_t complexity;

		constexpr subnfa(const subnfa&) noexcept = default;
		constexpr subnfa(edge begin_edge, state_iterator_t end_state) noexcept: 
			begin_edge{begin_edge}, end_state{end_state} {}
		constexpr subnfa(edge begin_edge, state_iterator_t end_state, complexity_t complexity) noexcept: 
			begin_edge{begin_edge}, end_state{end_state}, complexity{complexity} {}


	};
	
	static constexpr int priority(oper op) noexcept{
		switch(op) {
		
		// useless, unary operators always have the highest priority
		// case oper::kleene   : 
		// case oper::positive :
		// case oper::optional : 
		// case oper::brackets :
		// case oper::brackets_invert:
		// case oper::braces   :  
		// 	return 0;
		case oper::concat   : return -1; // (concatenation)
		case oper::alter    : return -2; // |
		case oper::lparen   : return -3; // (
		default: return numeric_limits<int>::min();
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
		default:  return oper::bad_oper;
		}
	}


protected:
	
	// we don't directly use stack cause sometimes we need to assess the second top element of the stack,
	// but don't want to pop the top, access it and push it back. 
	struct nfa_stack_t: public stack<subnfa, vector<subnfa>> {
		using stack_t = stack<subnfa, vector<subnfa>>;

		// it is UB if size() < 2
		constexpr typename stack_t::const_reference second_top() const{
			// return this->c[size() - 2]; 
			return *++this->c.crbegin(); // slightly released inner container constrain
		}
		constexpr typename stack_t::reference second_top() {
			// return this->c[size() - 2];
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
		build_result = error_category::ready;
	}
	
	state_iterator_t top_begin_state() {
		assert(!nfa_stack.empty() && !states.empty());
		return nfa_stack.has_second_top() ? std::next(nfa_stack.second_top().end_state) : states.begin();
	}

	template <typename... Args>
	state_iterator_t new_state(Args&&... args) {
		states.emplace_back(forward<Args>(args)...);
		return --states.end();
	}
	template <typename... Args>
	state_iterator_t insert_new_state(state_iterator_t it, Args&&... args) {
		return states.insert(it, state{forward<Args>(args)...});
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
				
				// end_state->flag.loopback_end = true;
				end_state->flag |= state_flag::loopback_end;
				end_state->add_outgoing(begin_edge);
				begin_edge = edge::make_epsilon(end_state);
				complexity += 1;
				
				break;
			}
			// unary operator +, ψ(R+) = ψ(R) + 1
			case oper::positive: { 
				if(nfa_stack.empty()) return false;
				auto& [begin_edge, end_state, complexity] = nfa_stack.top();
				
				end_state->flag |= state_flag::loopback_end;
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
				auto branch_state = insert_new_state(top_begin_state(), state_flag::alternative_begin);

				branch_state->add_outgoing(pre_begin_edge)
					        ->add_outgoing(begin_edge);

				auto merge_state = new_state();
				pre_end_state->add_outgoing(edge::make_branch_end(0, merge_state));
				end_state->add_outgoing(edge::make_branch_end(1, merge_state));

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

	optional<edge> lex_escape(pattern_iterator_t& pos, const pattern_iterator_t& end) {
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
		assert(pos != end);

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

	tuple<error_category, pattern_iterator_t> parse(pattern_view_t s) {
		// shunting yard algorithm

		reset();
		
		if(s.empty()) return {build_result = error_category::empty_pattern, nullptr};

		bool has_potential_concat_oper = false;
		auto end = s.end();
		for(auto pos = s.begin(); pos < end;) {
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
				if(++pos == end) return {build_result = error_category::missing_paren, pos};
				if(auto result = parse_left_parenthesis(pos, end); result != error_category::success)
					return {build_result = result, pos}; 

				has_potential_concat_oper = false;
				break;
			}
			case ')': {
				while(
					!oper_stack.empty() && 
					(static_cast<underlying_type_t<oper>>(oper_stack.top()) & (static_cast<underlying_type_t<oper>>(oper::lparen))) == 0
				) {

					if(!reduce()) return {build_result = error_category::empty_operand, pos};
					oper_stack.pop();
				}

				if(oper_stack.empty()) return {build_result = error_category::missing_paren, pos}; // error: missing left paren '('
				// the top of oper_stack must be lparen like: (, (?:, (?=, (?!, 
				else if(auto result = reduce_left_parenthesis(pos, end); result != error_category::success) return {build_result = result, pos};
				oper_stack.pop();
				++pos;
				has_potential_concat_oper = true;
				break;
			}
			case '[': {
				// [c...] bracket expression
				if(++pos == end) return {build_result = error_category::bad_bracket_expression, pos};
				bool invert_range = false;
				if(*pos == '^') {
					invert_range = true;
					++pos;
				}
				if(auto brackets_res = parse_brackets(pos, end); brackets_res.has_value()) {
					if(has_potential_concat_oper && !reduce_concat()) return {build_result = error_category::empty_operand, pos};

					if(!invert_range) reduce_brackets(brackets_res.value());
					else              reduce_brackets_invert(brackets_res.value()); 
				}else return {build_result = error_category::bad_bracket_expression, pos};
				
				has_potential_concat_oper = true;
				break;

			}
			case '{': {
				// {m}, {m,}, {m,n}  counted repetition expression
				auto braces_res = parse_braces(++pos, end);
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
					if(auto lex_res = lex_escape(++pos, end); lex_res.has_value()) 
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
				return {build_result = error_category::missing_paren, end};
			}else if(!reduce()) {
				return {build_result = error_category::empty_operand, end};			
			}
			oper_stack.pop();
		}

		// is the element count of nfa_stack possible to be more then 1?
		assert(nfa_stack.size() == 1);

		insert_new_state(states.begin())->add_outgoing(nfa_stack.top().begin_edge);

		final_state = nfa_stack.top().end_state;

		// assign states' id
		state_id_t id = 0;
		for(auto& s: states) s.id = id++;

		while(!nfa_stack.empty()) nfa_stack.pop();

		return {build_result = error_category::success, end};
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

	error_category reduce_left_parenthesis(pattern_iterator_t& pos, const pattern_iterator_t& end) {
		if(nfa_stack.empty()) return error_category::empty_operand;
		switch(oper_stack.top()) {
		case oper::lparen: {	
			if(nfa_stack.size() < 2) return error_category::empty_operand; 
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
		case oper::lparen_non_marking:
			// do nothing
			break;
		case oper::lparen_positive_lookahead: 
			// TODO?
			return error_category::unsupported_features;
			break;
		case oper::lparen_negative_lookahead:
			// TODO?
			return error_category::unsupported_features;
			break;
		}
		return error_category::success;
	}

	error_category parse_left_parenthesis(pattern_iterator_t& pos, const pattern_iterator_t& end) {
		// assert '(' is comsumed and pos != end

		if(*pos != '?') {
			// is marking group
			++max_capture_id;
			auto dummy_state = new_state();
			edge capture_begin = edge::make_capture(max_capture_id, {}, dummy_state);
			
			nfa_stack.emplace(capture_begin, dummy_state, 1);
			oper_stack.push(oper::lparen);
			return error_category::success;
		}
		if(++pos == end) return error_category::missing_paren;  // (?
		switch(*pos++) {
		case ':': // grouping
			oper_stack.push(oper::lparen_non_marking);
			break;
		case '=': // zero-width positive lookahead
			oper_stack.push(oper::lparen_positive_lookahead);
			break;
		case '!': // zero-width negative lookahead
			oper_stack.push(oper::lparen_negative_lookahead);
			break;
		default:  // error: empty operand
			return error_category::empty_operand; // (?..
		}

		return error_category::success;
	}

	optional<vector<edge>> parse_brackets(pattern_iterator_t& pos, const pattern_iterator_t& end) {
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
			auto pre_state = insert_new_state(post_state, state_flag::conjunction_begin);

			for(auto& e: edges) {
				pre_state->add_outgoing(e.invert().set_target(post_state));
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

		static constexpr braces_result make_error() noexcept{
			return {error};
		}

		friend constexpr bool operator==(const braces_result& l, const braces_result& r) noexcept{
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
		// we probaly need to do something on the runtime machine, add more things to state_context
		return false; 
	}

	// TODO: in the consideration of optimization, let it can create more than one copy, which allows us reuse memo. 
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
			memo[it] = insert_new_state(begin_state, it->flag);
		}
		memo[end_state] = insert_new_state(begin_state, end_state->flag);

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

	braces_result parse_braces(pattern_iterator_t& pos, const pattern_iterator_t& end) {
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

	error_category get_result() const noexcept{
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

}; // nfa_builder

template <typename CharT>
struct non_determinstic_finite_automaton {
	// output of nfa_builder, 
	// a non-determinstic-finite-automaton(NFA)

	// NFA M = (Q, Σ, δ, q0, f) 
	using char_t = CharT; // Σ
	using range_t = char_range<char_t>;
	// using string_view_t = basic_string_view<char_t>;
	// using string_iterator_t = typename string_view_t::iterator;	
	
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
			size_t branch_id;
		} data;

		static constexpr bool is_word(char_t c) noexcept{
			return 
				in_range('0', '9', c) || 
				in_range('a', 'z', c) || 
				in_range('A', 'Z', c) || 
				(c == '_');		
		}
		static constexpr bool is_newline(char_t c) noexcept{
			return c == '\n' || c == '\r';
		}

		bool accept(char_t c) const noexcept{
			switch(category) {
			// case edge_category::epsilon: 
			// 	return false; 
			case edge_category::single_char: // range of one char [from]
				return c == data.single_char;
			case edge_category::range:       // range: [from-to]
				return in_range(data.range, c);
			case edge_category::spaces:      // space chars: [\t\n\v\f\r ] == [\x09-\x0d ]
				return in_range('\x09', '\x0d', c) || c == ' ';
			case edge_category::words:       // identifier chars(words): [0-9a-zA-Z_]
				return is_word(c);
			case edge_category::digits:      // digit chars: [0-9]
				return in_range('0', '9', c);
			case edge_category::newlines:
				return is_newline(c);
			case edge_category::all:
				return true;
			// invert ranges 
			case edge_category::non_newlines:       // [^\n\r]
				return !is_newline(c);
			case edge_category::invert_single_char: // [^c]
				return c != data.single_char;
			case edge_category::invert_range:       // [^from-to]
				return !in_range(data.range, c);
			case edge_category::non_spaces:         // [^\t\n\v\f\r ]
				return !in_range('\x09', '\x0d', c) && c != ' ';
			case edge_category::non_words:          // [^0-9a-zA-Z_]
				return !is_word(c);
			case edge_category::non_digits:         // [^0-9]
				return !in_range('0', '9', c);
			case edge_category::none:
				return false;
			default:
				return false;
			}

		}
		
		// TODO
		// // notice that tail is the previous position of end
		// // which means that the string range is [begin, tail]
		// bool assertion_accept(string_iterator_t pos, string_iterator_t begin, string_iterator_t tail) const noexcept {
		// 	switch(category) {			
		// 	case edge_category::assert_line_begin:
		// 		return pos == begin || is_newline(*std::prev(pos));
		// 	case edge_category::assert_line_end:
		// 		return pos == tail || is_newline(*std::next(pos)); 
		// 	case edge_category::assert_word_boundary: {
		// 		if(pos == begin || pos == tail) return is_word(*pos);
		// 		auto prev = *std::prev(pos);
		// 		return is_word(prev) ^ is_word(*pos); 
		// 	}
		// 	case edge_category::assert_non_word_boundary: {

		// 		if(pos == begin || pos == tail) return !is_word(*pos);
		// 		auto prev = *std::prev(pos);
		// 		return !(is_word(prev) ^ is_word(*pos));
		// 	}
		// 	// I have no idea for implement them now, 
		// 	// especially we have to handle a dozen of complicated cases 
		// 	case edge_category::assert_positive_lookahead:
		// 		[[fallthrough]];
		// 	case edge_category::assert_negative_lookahead:
		// 		[[fallthrough]];
		// 	default:
		// 		return true; // no assertion
		// 	}
		// }
		
		bool accept_epsilon() const noexcept{
			return (static_cast<underlying_type_t<edge_category>>(category) & 
		           static_cast<underlying_type_t<edge_category>>(edge_category::epsilon)) != 0; 	
		}

		bool is_epsilon() const noexcept{
			return category == edge_category::epsilon;
		}

		bool is_single_char() const noexcept{
			return category == edge_category::single_char || category == edge_category::invert_single_char;
		}

		bool is_range() const noexcept{
			return category == edge_category::range || category == edge_category::invert_range;
		}

		bool is_capture_begin() const noexcept{
			return category == edge_category::capture_begin;
		}

		bool is_assertion() const noexcept{
			return static_cast<underlying_type_t<edge_category>>(category) &
			       static_cast<underlying_type_t<edge_category>>(edge_category::assertion_mask) != 0;
		}

		capture_info get_capture() const noexcept{
			assert(is_capture_begin());
			return data.capture;
		}


	}; // struct edge

	struct state {
		
		state_flag flag;
		vector<edge> edges;

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

	using char_t = CharT;

	using string_t = basic_string<char_t>;
	// immutable
	using string_view_t = basic_string_view<char_t>;
	// mutable
	using pos_t = char_t*;
	using const_pos_t = const char_t*;

	using nfa_t = non_determinstic_finite_automaton<char_t>;

	using state_id_t = typename nfa_t::state_id_t;
	using group_id_t = size_t;

	// stores the contexts of captures in running nfa
	// use during runtime
	struct state_context {

		struct capture {

			// capture range: [begin, end)
			// begin == end represents empty string view ""
			
			// hard to use
			// view_iterator_t begin, end;
			// using const_pos_t = const char_t*;

			const_pos_t begin, end;

		protected:
			bool is_completed = false;
		public:

			constexpr capture() noexcept = default;
			constexpr capture(const_pos_t begin) noexcept: begin{begin} {}
			
			capture& reset(const_pos_t new_begin) noexcept{
				begin = new_begin;
				is_completed = false;
				return *this;
			}

			capture& complete(const_pos_t pos) noexcept{
				end = pos;
				is_completed = true;
				return *this;
			}

			bool try_complete(const_pos_t pos) noexcept{
				if(not is_completed) {
					 this->end = pos;
					 return is_completed = true;
				}
				return false;
			}

			bool completed() const noexcept{
				return is_completed;
			}

			template <default_initializable ResultViewT>
			requires constructible_from<ResultViewT, pos_t, pos_t>
			explicit operator ResultViewT() {
				return is_completed ? ResultViewT{const_cast<pos_t>(begin), const_cast<pos_t>(end)} : ResultViewT{};
			}
			
			template <default_initializable ResultViewT>
			requires constructible_from<ResultViewT, const_pos_t, const_pos_t>
			explicit operator ResultViewT() const {
				return is_completed ? ResultViewT{begin, end} : ResultViewT{};
			}


		}; // struct capture

		
		// group_id -> captures
		unordered_map<group_id_t, capture> captures;
		bool active = false;

		// // extra state data
		// union {
		// 	// active when state category == branch_end
		// 	size_t source_branch_id;
		// };


		state_context() = default;

		state_context& reset() noexcept{
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
	vector<state_context> next_state_contexts;
	unordered_map<state_id_t, unordered_set<group_id_t>> capture_end_states;

	const_pos_t begin, end, current;

public:

	regular_expression_engine(const nfa_t& nfa): nfa{nfa}, state_contexts(nfa.states.size()), next_state_contexts(nfa.states.size()) {
		assert(!nfa.states.empty());
	}

protected:

	regular_expression_engine& reset(const_pos_t new_begin, const_pos_t new_end) noexcept{
		for(auto& c: state_contexts) c.reset();
		for(auto& c: next_state_contexts) c.reset();
		state_contexts.front().active = true;
		current = begin = new_begin;
		end = new_end;
		return *this;
	}

	void update_contexts() noexcept{
		std::swap(state_contexts, next_state_contexts);
		for(auto& c: next_state_contexts) c.reset();
	}

	
	// compare contexts and returns whether we should replace the current context with propagator 
	constexpr bool needs_cover_context(const state_context& target, const state_context& propagator, const typename nfa_t::edge& e) const noexcept{
		
		if(!target.active) return true; 
		
		// always select the longest capture group
		for(group_id_t group_id = 1; group_id <= nfa.max_capture_id; ++group_id) {
			if(target.captures.find(group_id) == target.captures.cend()) return true; 
			if(propagator.captures.find(group_id) == propagator.captures.cend()) return false;
		}
		return true;

		// or destination state is not the end of branch structure
		// e.category != edge_category::branch_end ||
		// // or cover the context if current id is greater or equals to the propagator's
		// // e.data.branch_id: the branch id that the propagator passes
		// // current.source_branch_id: the branch id that current state passes
		// current.source_branch_id >= e.data.branch_id;
	}

	// propagate src's state_context to its target state by edges[edge_id]
	// it should support all kinds of edges, including ε edge
	template <bool shift_capture_pos = true, bool on_current_context = false>
	void propagate_context(state_context& src_context, const typename nfa_t::edge& e) {

		state_id_t dst = e.target;
		typename vector<state_context>::iterator dst_context_it;
		if constexpr(on_current_context) 
			dst_context_it = state_contexts.begin();
		else 
			dst_context_it = next_state_contexts.begin();
		
		std::advance(dst_context_it, dst);
		auto& dst_context = *dst_context_it;

		auto capture_pos = current;

		if constexpr(shift_capture_pos) ++capture_pos;

		if(needs_cover_context(dst_context, src_context, e)) {
			dst_context.active = true;

			switch(e.category) {
			case edge_category::capture_begin: {
				// is capture begin
				auto [group_id, capture_end] = e.get_capture();
				// propagate all of the context to the target state
				// or reset the context
				if(auto [begin_context_it, inserted] = dst_context.captures.try_emplace(group_id, capture_pos); inserted) {
					// capture new created
					// register the end state of this capture
					// TODO: should we dynamicly do it?
					// or build the map during nfa building time?
					capture_end_states[capture_end].insert(group_id);

				}else {
					// capture already exists, reset it
					// *begin_context_it: [group_id, capture]
					begin_context_it->second.reset(capture_pos);
				}

				// propagate source state context to the destnation state context if exists 
				// remove all remained bad contexts from dst_context first
				for(auto it = dst_context.captures.begin(); it != dst_context.captures.end();) {
					if(it->first != group_id) it = dst_context.captures.erase(it);
					else ++it;
				}

				// copy all of the new captures from src_context to dst_context
				for(auto [id, capture]: src_context.captures)
					if(id != group_id) 
						dst_context[id] = capture;

				break;
			}
			case edge_category::branch_end:
				// dst_context.source_branch_id = e.data.branch_id;
				[[fallthrough]];
			default:
				// normal edges
				dst_context.captures = src_context.captures;
			}
		}

		// complete all of the possible captures 
		if(auto it = capture_end_states.find(dst); it != capture_end_states.cend()) {
			for(auto id: it->second) // it->second: a set that stores all of the completed group ids on this destination state
				if(auto cap_it = dst_context.captures.find(id); cap_it != dst_context.captures.end()) 
					cap_it->second.try_complete(capture_pos);
		}
	}

	template <bool shift_capture_pos = true, bool on_current_context = false>
	void do_epsilon_closure(state_id_t state) {
		// apply ε-closure to state_contexts or next_state_contexts
		// all of the ε-closure(q) always maintains the same context? 
		// ε-closure(q) = {q} ∪ {p | p ∈ δ(q, ε) ∪ δ(δ(q, ε), ε) ∪ ...}	

		queue<state_id_t> que;
		unordered_set<state_id_t> visited{state};
		
		que.push(state);

		while(!que.empty()) {
			auto current_state = que.front();
			que.pop();

			for(const auto& e: nfa[current_state].edges) {
				if(!e.accept_epsilon()) continue;
				if(auto [it, inserted] = visited.emplace(e.target); inserted) {
					que.push(e.target);
					// propagate the state context if needed
					// notice that the source state context is current_state
					if constexpr(on_current_context)
						propagate_context<shift_capture_pos, on_current_context>(state_contexts[current_state], e);
					else
						propagate_context<shift_capture_pos, on_current_context>(next_state_contexts[current_state], e);
				}
			}
		}
	}

	bool step() {
		// we must reversely iterate runtime states
		bool trapped = true;
		auto state_it = nfa.states.rbegin();
		auto context_it = state_contexts.rbegin();
		// auto id = state_contexts.size() - 1;
		while(state_it != nfa.states.rend()) {
			if(!context_it->active) goto next_state; 

			if((state_it->flag & state_flag::conjunction_begin) != state_flag::none) {
				// conjunction state, all of the edges must be accepted
				// all of the edges point to the same target state
				for(const auto& e: state_it->edges) {
					if(!e.accept(*current)) goto next_state;
				}
				// all of the edges are accepted
				propagate_context(*context_it, state_it->edges.front());
				do_epsilon_closure(state_it->edges.front().target);
				trapped = false;
			}else {
				for(const auto& e: state_it->edges) if(e.accept(*current)) {
					propagate_context(*context_it, e);
					do_epsilon_closure(e.target);
					trapped = false;
				}
			}

			next_state:
			++state_it;
			++context_it;
			// --id;
		}

		return !trapped;
	}

	// void replace_impl(pos_t begin, pos_t end, vector<pair<pos_t, pos_t>>& holes, string_view_t replacement, size_t count) {
		
	// }

public:

	// match
	template <default_initializable ResultViewT = string_view_t, typename PosT> 
	requires 
		(convertible_to<PosT, pos_t> && constructible_from<ResultViewT, pos_t, pos_t>) ||
		(convertible_to<PosT, const_pos_t> && constructible_from<ResultViewT, const_pos_t, const_pos_t>)
	vector<ResultViewT> match(PosT begin, PosT end) {
		reset(begin, end);

		do_epsilon_closure<false, true>(0);

		while(current != end) {
			if(!step()) {
				// failed: can't match
				return {}; 
			}
			update_contexts();
			++current;
		}

		// failed: can't match
		if(!state_contexts[nfa.final_state].active) return {};

		vector<ResultViewT> result(nfa.max_capture_id + 1);
		// result[0] is the whole match
		result.front() = ResultViewT{begin, end};

		for(auto [group_id, capture]: state_contexts[nfa.final_state].captures) {
			result[group_id] = ResultViewT{capture};
		}
		return result;
	}

	template <typename ResultViewT = string_view_t, typename StringViewLikeT>
	requires requires(StringViewLikeT s) {
		{ s.size() } -> convertible_to<size_t>;
		requires 
			convertible_to<decltype(s.data() + s.size()), pos_t> || 
			convertible_to<decltype(s.data() + s.size()), const_pos_t>; 
	}
	vector<ResultViewT> match(StringViewLikeT s) {
		return match<ResultViewT>(s.data(), s.data() + s.size());
	}

	// search
	template <default_initializable ResultViewT = string_view_t, typename PosT>
	requires 
		(convertible_to<PosT, pos_t> && constructible_from<ResultViewT, pos_t, pos_t>) ||
		(convertible_to<PosT, const_pos_t> && constructible_from<ResultViewT, const_pos_t, const_pos_t>)
	vector<ResultViewT> search(PosT& pos, const_pos_t end) {
		while(pos != end) {
			reset(pos, end);
			do_epsilon_closure<false, true>(0);

			while(current != end) {
				if(!step()) break;
				++current;
				update_contexts();
			}
			
			if(!state_contexts[nfa.final_state].active) {
				// failed: can't match from this position
				++pos;
				continue;
			} 
			
			// matched
			vector<ResultViewT> result(nfa.max_capture_id + 1);
			// current is const_pos_t, but the input PosT probaly be non-const
			result.front() = ResultViewT{pos, const_cast<PosT>(current)};
			for(auto [group_id, capture]: state_contexts[nfa.final_state].captures) {
				result[group_id] = ResultViewT{capture};
			}

			// move it to the next begin
			pos = const_cast<PosT>(current);
			return result;

		}

		return {};
	}

	template <typename ResultViewT = string_view_t, typename StringViewLikeT>
	requires requires(StringViewLikeT s) {
		{ s.size() } -> convertible_to<size_t>;
		requires 
			convertible_to<decltype(s.data() + s.size()), pos_t> || 
			convertible_to<decltype(s.data() + s.size()), const_pos_t>; 
	}
	vector<ResultViewT> search(StringViewLikeT s) {
		auto pos = s.data();
		return search<ResultViewT>(pos, pos + s.size());
	}

	// search all: of the matches of pattern in the range [begin, end)
	template <default_initializable ResultViewT = string_view_t, typename PosT>
	requires 
		(convertible_to<PosT, pos_t> && constructible_from<ResultViewT, pos_t, pos_t>) ||
		(convertible_to<PosT, const_pos_t> && constructible_from<ResultViewT, const_pos_t, const_pos_t>)
	vector<vector<ResultViewT>> search_all(const_pos_t begin, const_pos_t end) {
		vector<vector<ResultViewT>> results;
		auto pos = begin;
		while(true) {
			// result will be empty if it == end
			auto result = search<ResultViewT>(pos, end); 
			if(result.empty()) break;
			results.push_back(result);
		}
		return results;
	}
	
	template <typename ResultViewT = string_view_t, typename StringViewLikeT>
	requires requires(StringViewLikeT s) {
		{ s.size() } -> convertible_to<size_t>;
		requires 
			convertible_to<decltype(s.data() + s.size()), pos_t> || 
			convertible_to<decltype(s.data() + s.size()), const_pos_t>; 
	}
	vector<vector<ResultViewT>> search_all(StringViewLikeT s) {
		return search_all<ResultViewT>(s.data(), s.data() + s.size());
	}
		
	// replace: the match of pattern for at most 'count' times with replacement 
	// returns the count of replacements
	size_t replace(pos_t& pos, const_pos_t end, string_view_t replacement, size_t count = -1) {
		size_t i = 0;
		for(; i < count; ++i) {
			auto result = search<pair<pos_t, pos_t>>(pos, end);
			if(result.empty()) break; // no more matches

			// only replace the first match, witch is the whole match
			auto& match = result.front();

			// FIXME: incorrect replacement when the replacement's length is not equal to match's length
			copy(replacement.cbegin(), replacement.cend(), match.first);
		}
		return i;
	}

	size_t replace(string_t& target, string_view_t replacement, size_t count = -1) {
		auto pos = target.data();
		return replace(pos, pos + target.size(), replacement, count);
	}


}; // struct regular_expression_engine

} // namespace impl

template <typename CharT>
using regular_expression_engine = impl::regular_expression_engine<CharT>;

// free functions
template <typename CharT, typename ResultViewT = std::basic_string_view<CharT> >
std::tuple<error_category, std::vector<ResultViewT>> match(std::basic_string_view<CharT> pattern, std::basic_string_view<CharT> target) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto errc = builder.get_result(); errc != error_category::success) 
	return {errc, {}};
	else return {
		errc, 
		regular_expression_engine<CharT>{builder.generate()}.template match<ResultViewT>(target)
	};
}

template <typename CharT, typename ResultViewT = std::basic_string_view<CharT> >
std::tuple<error_category, std::vector<ResultViewT>> search(std::basic_string_view<CharT> pattern, std::basic_string_view<CharT> target) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto errc = builder.get_result(); errc != error_category::success) 
		return {errc, {}};
	else return {
		errc, 
		regular_expression_engine<CharT>{builder.generate()}.template search<ResultViewT>(target)
	};
}

template <typename CharT, typename ResultViewT = std::basic_string_view<CharT> >
std::tuple<error_category, std::vector<std::vector<ResultViewT>> > search_all(std::basic_string_view<CharT> pattern, std::basic_string_view<CharT> target) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto errc = builder.get_result(); errc != error_category::success) 
		return {errc, {}};
	else return {
		errc, 
		regular_expression_engine<CharT>{builder.generate()}.template search_all<ResultViewT>(target)
	};
}

template <typename CharT>
std::tuple<error_category, size_t> replace(std::basic_string_view<CharT> pattern, std::basic_string<CharT>& target, std::basic_string_view<CharT> replacement, size_t count = -1) {
	impl::nfa_builder<CharT> builder{pattern};
	if(auto errc = builder.get_result(); errc != error_category::success) 
		return {errc, {}};
	else return {
		errc, 
		regular_expression_engine<CharT>{builder.generate()}.replace(
			target, 
			replacement, 
			count
		)
	};
}

template <typename CharT>
std::tuple<error_category, impl::non_determinstic_finite_automaton<CharT>> compile(std::basic_string_view<CharT> pattern) {
	impl::nfa_builder<CharT> builder{pattern};
	return {builder.get_result(), builder.generate()};
}

} // namespace regex

} // namespace rais
