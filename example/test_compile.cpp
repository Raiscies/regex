
#include <format>
#include <string>
#include <utility>
#include <iterator>
#include <iostream>


#include "../include/regular_expression.hpp"

template <typename... Args> 
void print(std::format_string<Args...> format, Args&&... args) {
	std::cout << std::format(format, std::forward<Args>(args)...);
}

int main(int argc, const char** argv) {
	using std::string;
	using std::distance;

	using namespace rais::regex;

	while(true) {
		
		string pattern = "";
		
		print("input a pattern:\n");
		std::cin >> pattern;

		print("pattern: {}\n", pattern);

		auto [result, nfa] = compile<char>(pattern);

		print("pattern result: {}\n", error_message(result));
		
		if(result != error_category::success) continue;
		regular_expression_engine<char> re{nfa};
		while(true) {
			string target;
			print("input a target string(input ~ to set a new pattern):\n");
			std::getline(std::cin, target);
			if(target == "~") break;
			auto result = re.match(target);
			print("target = {}, capture: [", target);
			size_t i = 0;
			for(const auto& m: result) {
				if(m.empty()) {
					print("\"\"[-,-]");
				}else {
					auto shift_dist = distance(std::as_const(target).data(), m.data());
					print("\"{}\"[{},{}]", m, shift_dist, shift_dist + m.size() - 1);
				}
				if(++i < result.size()) print(", ");
			}
			print("]\n");
		}
	}

	return 0;
}