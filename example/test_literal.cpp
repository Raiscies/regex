
#include "./common.hpp"

void print_results(auto results) {
    size_t r = 1;
    for(const auto& result: results) {
        println("{}. {}\n", r, result.empty() ? "[-]" : result[0]);

        r++;
    }
}

int main(int argc, const char** argv) {
    using std::string;
    using namespace rais::regex;
    using namespace rais::regex::literal;
    
    const string material(R"(
        Lorem ipsum dolor sit amet, consectetur adipiscing elit. 
        Etiam accumsan ultrices pellentesque. 
        Vestibulum sed leo tortor. 
        Aliquam erat volutpat. 
        Aenean ut felis mattis, mollis mi vel, interdum odio. 
        Integer viverra lacus quis quam varius, at imperdiet lacus ultricies. 
        Mauris porttitor pharetra dignissim. 
        Quisque vulputate nibh eget pharetra blandit. 
        Nulla eu eleifend augue. 
        Aliquam fringilla nulla a felis dignissim fringilla. 
        Donec sapien risus, molestie at pharetra vel, venenatis ut sem. 
        Fusce augue ante, tincidunt et mi sed, mattis semper urna. 
        Donec fermentum ipsum id efficitur hendrerit. 
        Pellentesque efficitur interdum semper. 
        Sed tristique massa eros, 
        nec pulvinar tortor mollis vitae. 
        Integer dapibus viverra ornare.
    )"); 

    auto lines = "\\s*(.+)\\s*\\n"_re.search_all(material);
    auto words = "\\w+"_re.search_all(material);
    auto capital_words = "[A-Z]\\w*"_re.search_all(material);

    println("lines: ");
    print_results(lines);
    println("words: ");
    print_results(words);
    println("capital words: ");
    print_results(capital_words);

}