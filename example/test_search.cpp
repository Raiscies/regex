
#include <format>
#include <string>
#include <utility>
#include <limits>
#include <iostream>
#include <string_view>

#include "../include/regular_expression.hpp"

template <typename... Args>
void print(std::format_string<Args...> format, Args&&... args) {
    std::cout << std::format(format, std::forward<Args>(args)...);
} 

int main(int argc, const char** argv) {
    using std::string;

    using namespace rais::regex;
    
    while(true) {
        string pattern;
        string target;
        print("input a pattern:\n");
        std::cin >> pattern;
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        print("input a target string:\n");
        std::getline(std::cin, target);

        print("pattern: {}\n", pattern);
        print("target: {}\n", target);

        auto [errc, result] = search<char>(pattern, target);
        if (errc != error_category::success) {
            print("error: {}\n", error_message(errc));
            continue;
        }
        print("pattern result: {}\n", error_message(errc));
        size_t i = 0;
        for(const auto& m: result) {
            if(m.empty()) {
                print("\"\"[-,-]");
            }else {
                auto shift_dist = std::distance(std::as_const(target).data(), m.data());
                print("\"{}\"[{},{}]", m, shift_dist, shift_dist + m.size() - 1);
            }
            if(++i < result.size()) print(", ");
        }
        print("\n");

    }
}