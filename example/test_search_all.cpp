
#include "./common.hpp"

int main(int argc, const char** argv) {
    using std::string;

    using namespace rais::regex;
    
    while(true) {
        string pattern;
        string target;
        println("input a pattern:");
        std::cin >> pattern;
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        println("input a target string:");
        std::getline(std::cin, target);

        println("pattern: {}", pattern);
        println("target: {}", target);

        auto [errc, results] = search_all<char>(pattern, target);
        if (errc != error_category::success) {
            println("error: {}", error_message(errc));
            continue;
        }
        println("pattern result: {}", error_message(errc));

        size_t r = 1;
        if(results.empty()) {
            println("no match found.");
            continue;
        }
        for(const auto& result: results) {
            size_t i = 0;
            println("{}. ", r);
            for(const auto& m: result) {
                
                if(m.empty()) {
                    print("\"\"[-,-]");
                }else {
                    auto shift_dist = std::distance(std::as_const(target).data(), m.data());
                    print("\"{}\"[{},{}]", m, shift_dist, shift_dist + m.size() - 1);
                }
                if(++i < result.size()) print(", ");
            }
            println("");
            r++;
        }
        
    }
}