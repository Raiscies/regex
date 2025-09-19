

#include "./common.hpp"

int main(int argc, const char** argv) {
    using std::string;

    using namespace rais::regex;
    
    while(true) {
        string pattern;
        string replacement;
        string target;

        println("input a pattern:");
        std::cin >> pattern;
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');

        println("input a replacement string:");
        std::cin >> replacement;
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        
        println("input a target string:");
        std::getline(std::cin, target);

        println("pattern: \"{}\" -> replacement: \"{}\"", pattern, replacement);
        println("target: {}", target);

        auto [errc, result] = replace<char>(pattern, target, replacement);
        if (errc != error_category::success) {
            println("error: {}", error_message(errc));
            continue;
        }
        println("pattern result: {}", error_message(errc));
        println("after replacing: \n{}", target);

    }
}