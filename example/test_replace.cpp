

#include <format>
#include <string>
#include <limits>
#include <utility>
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
        string replacement;
        string target;

        print("input a pattern:\n");
        std::cin >> pattern;
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');

        print("input a replacement string:\n");
        std::cin >> replacement;
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        
        print("input a target string:\n");
        std::getline(std::cin, target);

        print("pattern: \"{}\" -> replacement: \"{}\"\n", pattern, replacement);
        print("target: {}\n", target);

        auto [errc, result] = replace<char>(pattern, target, replacement);
        if (errc != error_category::success) {
            print("error: {}\n", error_message(errc));
            continue;
        }
        print("pattern result: {}\n", error_message(errc));
        print("after replacing: \n{}\n", target);

    }
}