
/*
	Regular Expression Interpreter by Raiscies.
	
	Supported Grammer:
	concat
	select            | 
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
#include <stack>
#include <queue>
#include <vector>
#include <string>
#include <limits>
#include <utility>
#include <cstddef>
#include <optional>
#include <iostream>
#include <functional>
#include <string_view>
#include <unordered_map>

#include "fmt/core.h"

namespace rais {

using std::cin;
using std::map;
using std::set;
using std::get;
using std::pair;
using std::swap;
using std::tuple;
using std::queue;
using std::stack;
using std::size_t;
using std::string;
using std::vector;
using std::optional;
using std::in_place;
using std::string_view;
using std::basic_string;
using std::unordered_map;
using std::numeric_limits;
using std::reference_wrapper;
using std::basic_string_view;

template <typename CharT>
struct char_range {
	using char_t = CharT;
	char_t from, to;
};

template <typename CharT>
constexpr bool in_range(CharT a, CharT b, CharT x) noexcept{ return a <= x && x <= b; }

template <typename CharT>
constexpr bool in_range(const char_range<CharT>& r, CharT x) noexcept { return in_range(r.from, r.to, x); }


template <typename CharT>
struct non_determinstic_automaton {
	// a non-determinstic-finite-automaton(NFA)


	// NFA M = (Q, Σ, δ, q0, F) 
	using char_t = CharT; // Σ
	using string_view_t = basic_string_view<char_t>;
	using range_t = char_range<char_t>;

	using state_t = size_t;

	using state_set_t = set<state_t>; // type of Q or Q's subset

	using final_state_set_t = state_set_t; // F: is a subset of Q

	using result_t = vector<string_view_t>;

	struct edge {
		
		// char_t from, to;
		enum class range_category: char {
			epsilon     = 0, // empty edge
			single_char = 1, // range of one char [from]
			range       = 2, // range: [from-to]
			spaces      = 3, // space chars: [\f\n\r\t\v]
			words       = 4, // identifier chars(words): [0-9a-zA-Z_]
			digits      = 5, // digit chars: [0-9]
			newlines    = 6, // [\n\r](currently unused)
			all         = 7, // any chars


			// some special edge, for internal implementation
			conjunction_range = 8, // a flag to mark the start state of this edge requires all of the edges it come from are accepted (conjunction)

			// identify the begin of sub-nfa, for capture grammer "(R)" 
			// greedy or not non-greedy
			greedy_capture_begin = 9, 
			nongreedy_capture_begin = 10,
			
			// invert ranges 
			invert_single_char = -single_char,  // [^c]
			invert_range       = -range,        // [^from-to]
			non_spaces         = -spaces,       // [^\f\n\r\t\v]
			non_words          = -words,        // [^0-9a-zA-Z_]
			non_digits         = -digits,       // [^0-9]

			non_newlines       = -newlines,     // [^\n\r] (wildcard)

			none               = -all           // nothing could be accepted

		} category;

		
		union{
			// active when category == single_char
			char_t single_char; 
			// active when category == range
			range_t range;
			// active when category == epsilon
			state_t capture_end;
		};


		state_t target_state = -1;

		constexpr edge(state_t target = -1) noexcept: 
			category{range_category::epsilon}, target_state{target} {} // an empty(epsilon) edge

		constexpr edge(range_category category_, state_t target = -1) noexcept: 
			category{category_}, target_state{target} {}

		constexpr edge(char_t c, bool invert_range_ = false, state_t target = -1) noexcept: 
			category{invert_range_ ? range_category::invert_single_char : range_category::single_char}, single_char{c}, target_state{target} {}
			
		constexpr edge(char_t from_, char_t to_, bool invert_range_ = false, state_t target = -1) noexcept: 
			category{invert_range_ ? range_category::invert_range : range_category::range}, range{from_, to_}, target_state{target} {}
		
		constexpr edge(const edge&) noexcept = default;
		constexpr edge(const edge& other, state_t target) noexcept: edge{other} {
			target_state = target;
		}

	private:
		constexpr edge(bool greedy, state_t target, state_t capture_end_) noexcept:
			category{greedy ? range_category::greedy_capture_begin : range_category::nongreedy_capture_begin}, 
			capture_end{capture_end_}, 
			target_state{target} {}
	public:

		static constexpr edge make_epsilon(state_t target = -1) noexcept{
			return {target};
		}
		static constexpr edge make_capture(bool greedy, state_t target, state_t capture_end) noexcept{
			return {greedy, target, capture_end};
		}
		static constexpr edge make_conjunction(state_c target = -1) noexcept{
			return {range_category::conjunction_range, target};
		}
		

		bool accept(char_t c) const noexcept{
			switch(category) {
			case range_category::epsilon: 
			case range_category::greedy_capture_begin:
			case range_category::nongreedy_capture_begin:
				return false; 
			case range_category::single_char: // range of one char [from]
				return c == single_char;
			case range_category::range:       // range: [from-to]
				return in_range(range, c);
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
			case range_category::non_newlines:       // [^\n\r]
				return c != '\n' && c != '\r';
			case range_category::invert_single_char: // [^c]
				return c != single_char;
			case range_category::invert_range:       // [^from-to]
				return !in_range(range, c);
			case range_category::non_spaces:         // [^\t\n\v\f\r]
				return !in_range('\x09', '\x0d', c);
			case range_category::non_words:          // [^0-9a-zA-Z_]
				return not( 
					in_range('0', '9', c) || 
			    	in_range('a', 'z', c) || 
			    	in_range('A', 'Z', c) || 
			    	(c == '_'));
			case range_category::non_digits:         // [^0-9]
				return !in_range('0', '9', c);
			case range_category::none:
				return false;
			default:
				return false;
			}

		}
		bool accept_epsilon() const noexcept{
			switch(category) {
				case range_category::epsilon:
				case range_category::greedy_capture_begin:
				case range_category::nongreedy_capture_begin:
					return true;
				default: 
					return false;
			} 	
		}
		edge& set_target(state_t index) noexcept{
			target_state = index;
			return *this;
		}

		edge& set_range(char_t from_, char_t to_, bool invert_range_ = false) noexcept{
			// from = from_;
			// to = to_;
			range = {from_, to};
			category = invert_range_ ? range_category::invert_range : range_category::range;
			return *this;
		}
		edge& set_range(char_t c, bool invert_range_ = false) noexcept{
			single_char = c;
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

		bool is_capture_start() const noexcept{
			return category == range_category::greedy_capture_begin || 
			       category == range_category::nongreedy_capture_begin;
		}

		bool is_greedy_capture() const noexcept{
			return category == range_category::greedy_capture_begin;
		}
		bool is_non_greedy_capture() const noexcept{
			return category == range_category::nongreedy_capture_begin;
		}

	}; // struct edge

	// stores the contexts of captures in running nfa
	struct capture_contexts {

		struct capture_context_item {
			const edge& begin;  // the begin of a sub-nfa
			const state_t end;  // the end of a sub-nfa
			const greedy;

			char_t* capture_begin = nullptr, 
			      * capture_end = nullptr;
			bool completed = false;

			constexpr capture_contexts(const edge& begin_) noexcept: begin{begin_}, end{begin_.capture_end}, greedy{begin.is_greedy_capture()} {}

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
					return {capture_begin, capture_end};
				else 
					return {};
			}

		}; 

		unordered_map<reference_wrapper<const edge>, capture_context_item> contexts;
		unordered_map<state_t, reference_wrapper<capture_context_item>> contexts_ref_by_state;

		bool new_context(const edge& e) {
			auto [it, inserted] contexts.try_emplace(e, e);
			if(inserted) {
				contexts_ref_by_state.try_emplace(e.capture_end, *it);
			}

			return inserted;
		}

		// reset context by the edge if it's already exists, or else create a new context
		void reset_capture(const edge& e, const char_t* capture_begin = nullptr) {
			if(not new_context(e)) {
				contexts[e].reset_capture(capture_begin);
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
			if(contexts.count(e) != 0) {
				contexts[e].complete_capture(capture_end);
				return true;
			}
			return false;
		}
		bool try_complete_capture(state_t end_state, const char_t* capture_end) {
			if(contexts_ref_by_state.count(end_state) != 0) {
				contexts_ref_by_state[end_state].complete_capture(capture_end);
				return true
			}
			return false;
		}

		capture_context_item& get_context(const edge& e) {
			return contexts[e];
		}
		capture_context_item& get_context(state_t end_state) {
			return contexts_ref_by_state[e]
		}

		result_t get_result() const{
			result_t captures;
			for(capture_context_item& context: contexts) {
				if(context.completed) 
					captures.push_back(context.get_capture());
			}
			return captures;
		}

	}; // struct capture_contexts


	// δ: Q * (Σ ∪ {ε}) -> 2^Q
	struct transform_t {

		// accept (state-space(q), {character-space(c)}) -> {state-space(q)}
		vector<vector<edge>> m;
		// capture_context context;

		// do_epsilon_closure, without capture_contexts
		state_set_t& do_epsilon_closure(state_set_t& current_states) const{
			// do ε-closure(current_states) and assign to itself
			state_set_t current_appended_states = current_states, 
			               next_appended_states;
			while(true) {
				for(state_t q: current_appended_states) {
					for(const edge& e: m[q]) {
						if(e.accept_epsilon() && current_states.count(e.target_state) == 0) {
							// e links to a new state that does not in current_states set
							next_appended_states.insert(e.target_state);

						}
					}
				}
				if(next_appended_states.empty()) return current_states;

				current_states.insert(next_appended_states.begin(), next_appended_states.end());
				current_appended_states = std::move(next_appended_states);
				next_appended_states.clear();
			}
		}

		state_set_t& do_epsilon_closure(state_set_t& current_states, const char_t* pos, capture_contexts& contexts) const{
			// do ε-closure(current_states) and assign to itself
			state_set_t current_appended_states = current_states, 
			               next_appended_states;
			while(true) {
				for(state_t q: current_appended_states) {
					for(const edge& e: m[q]) {
						if(e.accept_epsilon() && current_states.count(e.target_state) == 0) {
							// e links to a new state that does not in current_states set
							next_appended_states.insert(e.target_state);

							// handle capture
							if(e.is_capture_start()) {
								contexts.reset_capture(e, pos);
							}
						}
					}
				}
				if(next_appended_states.empty()) return current_states;

				current_states.insert(next_appended_states.begin(), next_appended_states.end());
				current_appended_states = std::move(next_appended_states);
				next_appended_states.clear();
			}
		}

		// without capture_contexts
		state_set_t operator()(const state_set_t& current_states, char_t c) const{
			// assume ε-closure(current_states) == current_states

			if(current_states.empty()) return {};
			state_set_t new_states;

			for(auto q: current_states) {
				// for each protential current state
				if(m[q].empty()) continue;
				else if(auto first_edge = m[q][0], first_edge.is_conjunction_range()) {
					// this state and its edges are conjunction
					// c is accepted only when all of the edges are accepted 
					for(auto it = ++m[q].cbegin(); it != m[q].cend(); ++it)
						if(!it->accept(c)) goto next_state;

					// this conjunction range is accepted
					new_states.insert(first_edge.target_state);

					next_state:;
				}else {
					for(const edge& e: m[q]) {
						// for each range
						if(e.accept(c)) {
							new_states.insert(e.target_state);
						}
					} 
				}
			}
			return do_epsilon_closure(new_states);
		}

		state_set_t operator()(const state_set_t& current_states, const char_t* pos, capture_contexts& contexts) const{
				// assume ε-closure(current_states) == current_states

			if(current_states.empty()) return {};
			state_set_t new_states;
			char_t c = *pos;

			for(auto q: current_states) {
				// for each protential current state
				if(m[q].empty()) continue;
				else if(auto first_edge = m[q][0], first_edge.is_conjunction_range()) {
					// this state and its edges are conjunction
					// c is accepted only when all of the edges are accepted 
					for(auto it = ++m[q].cbegin(); it != m[q].cend(); ++it)
						if(!it->accept(c)) goto next_state;

					// this conjunction range is accepted
					new_states.insert(first_edge.target_state);
					contexts.try_complete_capture(first_edge.target_state);

					next_state:;
				}else {
					for(const edge& e: m[q]) {
						// for each range
						if(e.accept(c)) {
							new_states.insert(e.target_state);

							// try to complete the state if it is a end state of a sub nfa,
							// or else do nothing.
							contexts.try_complete_capture(e.target_state, pos);
						}
					} 
				}
			}
			return do_epsilon_closure(new_states, pos, contexts);
		}

	}; // struct transform_t




private:
	state_t max_state_index = 0;

public:
	// static constexpr state_t trap_state = state_t(-1);

	transform_t delta;
	final_state_set_t final_states;

	non_determinstic_automaton() {
		new_state();	
	}

	void reset() {
		delta.m.clear();
		final_states.clear();
		max_state_index = 0;
		delta.m.emplace_back();
	}

	state_t new_state() {
		delta.m.emplace_back();
		return ++max_state_index;
	}
	state_t new_state(const vector<edge>& edges) {
		delta.m.emplace_back(edges);
		return ++max_state_index;
	}

	void mark_final_state(state_t index) {
		final_states.insert(index);
	}

	bool bind_transform(state_t index, state_t target_index, const edge& e) {
		if(index > max_state_index or target_index > max_state_index) return false;

		delta.m[index].push_back(e.set_target(target_index)); // reset target
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

	tuple<edge, state_t> copy_sub_expression(edge e, state_t q) {
		// deep copy the sub expression from edge e to state q
		// assume e and q is valid
		// traverse the directed graph  -e-> ... > q

		edge e_copy {e, new_state()};
		if(e.target_state == q) {
			// delta.m.emplace_back();
			for(auto& edge_from_q: delta.m[q]) {
				if(edge_from_q.target_state == q) 
					delta.m[e_copy.target_state].emplace_back(edge_from_q, e_copy.target_state);
			}
			return {e_copy, e_copy.target_state};
		}

		// delta.m.emplace_back(delta.m[e.target_state]); // index is e_copy.target_state
		delta.m[e_copy.target_state] = delta.m[e.target_state];

		map<state_t, state_t> memo{{e.target_state, e_copy.target_state}}; // [src_state_index] -> [copy_state_index]
		queue<state_t> que; 
		que.emplace(e_copy.target_state);
		state_t q_copy;
		while(!que.empty()) {
			auto copy = que.front();
			que.pop();
			
			// replace the target states
			for(auto& edge_from_copy: delta.m[copy]) {
				if(auto it = memo.find(edge_from_copy.target_state); it != memo.end()) {
					// don't need to create new state
					edge_from_copy.set_target(get<1>(*it));
				}else {
					// create new state
					state_t new_target = new_state(delta.m[edge_from_copy.target_state]);
					memo[edge_from_copy.target_state] = new_target; // register memo
					if(edge_from_copy.target_state != q)  // the edge list of the last state q should be copy at the end
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
			if(auto forward_res = memo.find(forward->target_state); forward_res != memo.end()) {
				forward->set_target(get<1>(*forward_res));
				++forward;
			}else {
				while(backward != forward) {
					if(auto backward_res = memo.find(backward->target_state); backward_res != memo.end()) {
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

	// only check if the target is acceptable, but not capture anything 
	bool test(string_view_t target, state_set_t start_states = {0}) const{
		if(start_states.empty()) return false;

		state_set_t current_states = std::move(delta.do_epsilon_closure(start_states));
		for(const auto c: target) {
			auto new_states = delta(current_states, c);
			if(new_states.empty()) return false; // this nfa does not accept target string
			current_states = std::move(new_states);
		}
		// check if (current_states ∪ F) != Φ
		for(auto q: current_states) {
			if(final_states.count(q) != 0) return true; // target was accepted
		}
		return false; // target is unacceptable

	}

	// try to match the whole target and capture sub strings
	result_t match(string_view_t target) const{

		// init capture contexts
		capture_contexts contexts;

		state_set_t current_states = {0};
		delta.do_epsilon_closure(current_states);

		for(const auto pos = target.cbegin(); pos != target.cend(); ++pos) {
			auto new_states = delta(current_states, pos, contexts);

			if(new_states.empty()) return {}; // nothing to match
			current_states = std::move(new_states);
		}

		for(auto q: current_states) {
			if(final_states.count(q) != 0) return contexts.get_result();
		}

		return {}; // target is unacceptable

	}

	result_t search(string_view_t target) const{

		capture_contexts contexts;

		state_set_t current_states;

		// naive!
		for(const auto s = target.cbegin(); s != target.cend();) {
			current_states.emplace(0);
			delta.do_epsilon_closure(current_states);

			for(const auto pos = s; pos != target.cend(); ++pos) {
				auto new_states = delta(current_states, *pos);
				if(new_states.empty()) {
					// not return false, but let s move to the next char, 
					// and try to match again
					goto next_pass;
				}

				current_states = std::move(new_states);
			}
			// once the regex is matched, stop matching the tailing strings and return the result
			for(auto q: current_states) {
				if(final_states.count(q) != 0) return contexts.get_result();
			}

			next_pass:
			// reset all of state set and contexts
			contexts.reset_all_captures()
			current_states.clear();
			++s;
		}

		return {};
	}

	// single step test
	state_set_t step(char_t c, state_set_t start_states) const{
		return delta(delta.do_epsilon_closure(start_states), c);
	}

	// single step match
	state_set_t step(const char_t* pos, state_set_t start_states, capture_contexts& contexts) const{
		return delta(delta.do_epsilon_closure(start_states), pos, contexts);
	}


}; // struct non_determinstic_automaton

template <typename CharT>
using NFA = non_determinstic_automaton<CharT>;

template <typename CharT, size_t max_unroll_complexity_ = 2000>
struct regular_expression {
	using char_t = CharT;
	using string_t = basic_string<char_t>;
	using string_view_t = basic_string_view<char_t>;

	// store the pattern capture result
	using capture_t = vector<string_view_t>; 

	using nfa_t = NFA<char_t>;
	using edge = typename nfa_t::edge;
	using state_t = typename nfa_t::state_t;

	using complexity_t = size_t;
	static constexpr complexity_t max_unroll_complexity = complexity_t(max_unroll_complexity_);
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

	// the 3rd data of a tuple is used to compute the edge-state pair(or sub expression)'s complexity 	
	using output_stack_t = stack<tuple<edge, state_t, complexity_t>>;

	//parsing output: NFA M = (Q, Σ, δ, q0, F) 
	nfa_t nfa;

	regular_expression(string_view_t pattern) {
		parse(pattern);
	}
	regular_expression() noexcept = default;

	enum error_category {
		success = 0,
		empty_operand, 
		bad_escape, 
		missing_paren,
		bad_bracket_expression,
		bad_brace_expression,
		expensive_brace_expression_unroll
	};

	enum match_mode {
		match, 
		search, 
		
	};

	enum class oper {
		// enum value represents the priority of the operators
		kleene,          // *
		positive,        // +
		optional,        // ?
		concat,          // (concatnation)
		select,          // |
		lparen,          // (
		rparen,          // ) the priority of right-paren is meanless
		wildcard,        // . the priority of wildcard is meanless
		brackets,        // [chars...]
		brackets_invert, // [^chars...]
		braces           // {m}, {m,}, {m,n}
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
		case oper::select   : return -2;
		case oper::lparen   : return -3;
		default: return -114514;
		}
	}
	static constexpr oper to_oper(char_t c) noexcept{
		switch(c) {
		case '*': return oper::kleene;
		case '+': return oper::positive;
		case '?': return oper::optional;
		case '|': return oper::select;
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

	// transform a regex pattern to a NFA
	pair<error_category, const char_t*> parse(string_view_t s) {
		// RE don't need to tokenize because each of the char (except of escape char sequences) is a token

		// shunting yard algorithm
		// operator priority:  *  > (concatnation) > |
		// supported operator: 
		// *,  |, (concatnation), ., 
		
		nfa.reset();
		
		if(s.empty()) return {success, nullptr};


		stack<oper> oper_stack;

		// stack<tuple<edge, state_t, complexity_t>> output_stack;
		output_stack_t output_stack;

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
				oper_stack.push(oper::lparen);
				++pos;
				has_potential_concat_oper = false;
				break;
			case ')':
				while(!oper_stack.empty() && oper_stack.top() != oper::lparen) {
					if(!reduce(output_stack, oper_stack.top())) {
						return {empty_operand, pos};
					}
					oper_stack.pop();
				}

				if(oper_stack.empty()) {
					// error: missing left paren '('
					return {missing_paren, pos};
				}else {
					// the top must be lparen '('
					reduce(output_stack, oper_stack.top());
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
					if(has_potential_concat_oper && !insert_concat_oper(output_stack, oper_stack)) return {empty_operand, pos};

					if(!invert_range) reduce_brackets(output_stack, brackets_res.value());
					else              reduce_brackets_invert(output_stack, brackets_res.value()); 
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
				if(!reduce_braces(output_stack, braces_res)) 
					return {expensive_brace_expression_unroll, pos};
				has_potential_concat_oper = true;
				break;
			}
			default: {
				// is character(s)/wildcard
				edge e;
				state_t q = nfa.new_state();
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
				output_stack.emplace(std::move(e), q, 1);
				
				has_potential_concat_oper = true;
				break;
			} // default
			} // switch
		}
		// clear stacks
		while(!oper_stack.empty()) {
			if(oper_stack.top() == oper::lparen) {
				// missing right paren ')'
				return {missing_paren, s.end()};
			}else if(!reduce(output_stack, oper_stack.top())) {
				
				return {empty_operand, s.end()};			
			}
			oper_stack.pop();
		}
		nfa.bind_transform(0, get<0>(output_stack.top())/*.first*/);
		nfa.mark_final_state(get<1>(output_stack.top())/*.second*/);
		return {success, s.end()};
	}

	bool insert_concat_oper(output_stack_t& output_stack, stack<oper>& oper_stack) {
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
		case 'b': return {'\b'}; // backspace // TODO: this works only when in bracket expression.
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

	bool reduce(output_stack_t& output_stack, oper op, const tuple<edge, state_t, complexity_t>& current_edge_state) {
		switch(op) {
		case oper::kleene: {  // *, ψ(e*) = ψ(e) + 1
			// unary operator
			auto& [e, q, psi] = current_edge_state;    
			nfa.bind_transform(q, e);              // q -e->...> q
			edge new_e {q};                           // new_e = -ε->
			output_stack.emplace(new_e, q, psi + 1);  // -new_e-> q
			break;
		}
		case oper::positive: { // +, ψ(e+) = 2ψ(e)
			// unary operator
			auto& [e, q, psi] = current_edge_state;
			nfa.bind_transform(q, e);             // -e->...> q -e->...> q
			output_stack.emplace(e, q, 2 * psi);     // -e->...> q
			break;
		} 
		case oper::optional: { // ?, ψ(e?) = ψ(e) + 2
			// unary operator
			auto& [e, q, psi] = current_edge_state;
			state_t new_q = nfa.new_state();
			nfa.bind_transform(new_q, e);
			nfa.bind_empty_transform(new_q, q);
			edge new_e = {new_q};
			output_stack.emplace(new_e, q, psi + 2);
			break;
		}
		case oper::concat: {  // (concatnation), ψ(e0 e1) = ψ(e0) + ψ(e1)
			if(output_stack.empty()) return false;
			// binary operator
			auto [e0, q0, psi0] = output_stack.top();
			auto& [e1, q1, psi1] = current_edge_state;
			output_stack.pop();
			nfa.bind_transform(q0, e1);                // q0 -e1->...> q1
			output_stack.emplace(e0, q1, psi0 + psi1);    // -e0->...> q0 -e1->...> q1
			break;
		}
		case oper::select: { // |, ψ(e0 | e1) = ψ(e0) + ψ(e1) + 3  
			if(output_stack.empty()) return false;
			// binary operator
			auto [e0, q0, psi0] = output_stack.top();
			auto& [e1, q1, psi1] = current_edge_state;
			output_stack.pop();
			state_t new_q = nfa.new_state();
			nfa.bind_empty_transform(q0, new_q);  // q0 -ε-> new_q
			nfa.bind_empty_transform(q1, new_q);  // q1 -ε-> new_q
			state_t new_q2 = nfa.new_state();     // create new_q
			nfa.bind_transform(new_q2, e0);       // new_q2 -e0->...> q0
			nfa.bind_transform(new_q2, e1);       // new_q2 -e1->...> q1
			edge new_e = {new_q2};                   // new_e = -ε->
			output_stack.emplace(new_e, new_q, psi0 + psi1 + 3);      // -new_e-> new_q2 -{-e0->...> q0, -e1->...> q1}-> new_q
			break;
		}
		case oper::lparen: { // (, ψ( (e) ) = ψ(e) + 1
			// insert a capture begin empty edge to the sub nfa
			auto [e, q, psi] = current_edge_state;
			state_t dummy_state = nfa.new_state();
			// capture_begin_e directly link the dummy state, and mark the parentess(right parentess) end to state q  
			edge capture_begin_e = edge::make_capture(true /* greedy */, dummy_state, q); // -(-> dummy_state ... q)  
			nfa.bind_transform(dummy_state, e); // dummy_state -e-> ... q 
			output_stack.emplace(capture_begin_e, q, psi + 1);
			break;
		}
		default: {
			// unknown operators
			return false;
		}
		}
		return true;
	}
	bool reduce(output_stack_t& output_stack, oper op) {
		if(output_stack.empty()) return false;
		auto top = output_stack.top();
		output_stack.pop();
		return reduce(output_stack, op, top);
	}

	// void reduce_parentess(output_stack_t& output_stack, )

	void reduce_brackets(output_stack_t& output_stack, vector<edge>& edges) {
		if(edges.empty()) {
			// []
			state_t new_q = nfa.new_state();
			// -x-> new_q
			// always not accept
			output_stack.emplace(edge{edge::range_category::none, new_q}, new_q, 1);
		}else if(edges.size() == 1) {
			// [r] == r
			state_t new_q = nfa.new_state();
			// ---> new_q
			output_stack.emplace(edges[0].set_target(new_q), new_q, 1);
		}else {
			// [R1...Rn]
			state_t new_q1 = nfa.new_state(), 
			        new_q2 = nfa.new_state();
			edge new_e = {new_q1}; // new_e: -ε-> new_q1
			// -ε-> new_q1 -{e1, e2, ...en}-> new_q2
			for(auto& e: edges) 
				nfa.bind_transform(new_q1, e.set_target(new_q2));

			output_stack.emplace(new_e, new_q2, edges.size() + 1);
		}
	}
	void reduce_brackets_invert(output_stack_t& output_stack, vector<edge>& edges) {
		if(edges.empty()) {
			// [^]
			state_t new_q = nfa.new_state();
			// ---> new_q
			// always accept
			output_stack.emplace(edge{edge::range_category::all, new_q}, new_q, 1);
		}else if(edges.size() == 1) {
			// [^r]
			state_t new_q = nfa.new_state();
			// -^e-> new_q
			output_stack.emplace(edges[0].invert().set_target(new_q), new_q, 1);
		}else {
			// [^R1...Rn]
			state_t new_q1 = nfa.new_state(), 
			        new_q2 = nfa.new_state();
			edge new_e = {new_q1}; // new_e: -ε-> new_q1

			// first edge of new_q1 is a persedo edge that identify it is a conjunction range
			nfa.bind_transform(new_q1, edge::make_conjunction(new_q2));
			// -ε-> new_q1 -{conjunction_flag, ^e1, ^e2, ...^en}-> new_q2
			for(auto& e: edges) 
				nfa.bind_transform(new_q1, e.invert().set_target(new_q2));

			output_stack.emplace(new_e, new_q2, edges.size() + 2);

		}
	}

	// counted loop 'R{n, m}' grammer
	bool reduce_braces(output_stack_t& output_stack, const tuple<int, size_t, size_t>& braces_res) {
		if(try_unroll_brace_expression(output_stack, braces_res)) {
			return true;
		}
		// TODO: implements counted repetition loop
		return false; 
	}

	bool try_unroll_brace_expression(output_stack_t& output_stack, const tuple<int, size_t, size_t>& braces_res) {
		// trivial algorithm:
		// e{m}   -> e...e            m times e
		// e{m,}  -> e...e+           m times e
		// e{m,n} -> e...e(e?)...(e?) m times e and n-m times (e?)
		auto [e, q, psi] = output_stack.top();
		complexity_t new_psi;
		// output_stack.pop();
		auto [brace_case, m, n] = braces_res;
		switch(brace_case) {
		case 3: // e{m,n}
			if(m != n) {
				new_psi = n * psi + n - m;
				if(new_psi > max_unroll_complexity) return false;
				output_stack.pop();

				state_t current_q = q;
				state_t final_q = nfa.new_state();
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
					nfa.bind_empty_transform(front_e.target_state, final_q);
					nfa.bind_transform(front_e.target_state, e);
					nfa.bind_empty_transform(current_q, final_q);
					for(size_t i = 0; i < n - 1; ++i) { // n != m => n != 0
						auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
						nfa.bind_transform(current_q, new_e);
						nfa.bind_empty_transform(new_q, final_q);
						current_q = new_q;
					}
					e = front_e;
				}
				output_stack.emplace(e, final_q, new_psi);
				break;
			} 
			// else m == n: e{m,m} = e{m}
			[[fallthrough]];
		case 1: // e{m}
			if(m == 0) {
				// e{0} == ε
				// simply ignore the edge e 
				output_stack.pop();
				output_stack.emplace(edge{q}, q, 1); // -ε-> q
			}else {
				new_psi = psi * m;
				if(new_psi > max_unroll_complexity) return false;
				output_stack.pop();

				state_t current_q = q;
				for(size_t i = 0; i < m - 1; ++i) {
					auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
					nfa.bind_transform(current_q, new_e);
					current_q = new_q;
				}
				output_stack.emplace(e, current_q, new_psi);
			}
			break;
		case 2: // e{m,}
			if(m == 0) {
				// e{0,} == e*
				output_stack.pop();
				nfa.bind_transform(q, e);                // q -e->...> q
				output_stack.emplace(edge{q}, q, psi + 1);  // -ε-> q
			}else {
				// e{m,} == e ... e+
				new_psi = (m + 1) * psi;
 				if(new_psi > max_unroll_complexity) return false;
				output_stack.pop();

				state_t current_q = q;
				for(size_t i = 0; i < m - 1; ++i) {
					auto [new_e, new_q] = nfa.copy_sub_expression(e, q);
					nfa.bind_transform(current_q, new_e);
					current_q = new_q;
				}
				nfa.bind_transform(current_q, edge{e, current_q});
				output_stack.emplace(e, current_q, new_psi);
			}
			break;
		}
		return true;

	}

	optional<vector<edge>> parse_brackets(typename string_view_t::const_iterator& pos, const typename string_view_t::const_iterator& end) {
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

		if(pos == end) {
			return {};
		}
		++pos;
		return edges;
	}

	// tuple<braces_case, upper, downer>
	tuple<int, size_t, size_t> parse_braces(typename string_view_t::const_iterator& pos, const typename string_view_t::const_iterator& end) {
		//              err, {m}, {m, }, {m, n}
		// braces_case: 0,   1,   2,     3 
		// m, n ::= [0-9]+
		auto lex_digits = [end](auto& p) {
			size_t n = 0;
			do{ n = n * 10 + size_t(*p++ - '0'); }while(p != end && in_range('0', '9', *p));
			return n;
		};

		int parse_stete = 0;
		size_t m, n = 0;
		while(pos != end && *pos != '}') {
			// if(*pos == ' ') {++pos; continue;} // spaces are not allowed
			switch(parse_stete) {
			case 0: 
				// lex the first arg: m
				if(in_range('0', '9', *pos)) {
					m = lex_digits(pos);
					++parse_stete;
				}else return {0, 0, 0}; // bad expression
				break;
			case 1:
				// lex comma: ,
				if(*pos != ',') return {0, 0, 0}; // bad expression
				++pos;
				++parse_stete;
				break;
			case 2:
				// lex the next arg: n
				if(in_range('0', '9', *pos)) {
					if(n = lex_digits(pos); m > n) return {0, 0, 0}; // {m, n}, m > n
					++parse_stete;
				}else return {0, 0, 0};// bad expression
				break;
			default:
				return {0, 0, 0}; // bad expression
			}
		}
		if(pos == end) return {0, 0, 0};
		// finished lexing braces expression
		++pos;
		return {parse_stete, m, n};
	}

	// // check if the target is fully match the regex 
	// auto match(string_view_t target) const noexcept -> capture_t {
		
	// }

	// // search the regex pattern from target
	// auto search(string_view_t target) const -> capture_t {

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

}; // struct regular_expression

} // namespace rais

int main(int argc, const char** argv) {
	if(argc <= 1) return 0;
	using namespace rais;

	fmt::print("pattern: {}\n", argv[1]);
	regular_expression<char> re;
	auto [parse_result, pos] = re.parse(argv[1]);
	fmt::print("pattern result: {}\n", re.error_message(parse_result));
	if(parse_result != regular_expression<char>::error_category::success) return 1;
	while(true) {
		string target;
		fmt::print("input a target string:\n");
		cin >> target;
		auto result = re.nfa.test(target);
		fmt::print("target = {}, result: {}\n", target, result);
	}
	fmt::print("passed.\n");

	return 0;
}