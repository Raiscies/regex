
#include "./common.hpp"

int main(int argc, const char** argv) {
	using std::string;
	using std::distance;

	using namespace rais::regex;

	while(true) {
		
		string pattern = "";
		
		println("input a pattern:");
		std::cin >> pattern;

		println("pattern: {}", pattern);

		auto [result, nfa] = compile<char>(pattern);

		println("pattern result: {}", error_message(result));
		
		if(result != error_category::success) continue;
		regular_expression_engine<char> re{nfa};
		while(true) {
			string target;
			println("input a target string(input ~ to set a new pattern):");
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
			println("]");
		}
	}

	return 0;
}