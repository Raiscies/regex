
# Regex  

This C++ project implements a simple regular expression engine for text manipulation.

This is a header-only project.  

## Getting Started

- Clone this repository and add the `./include/` path to your compiler's include search path.
- Include the main header file: 
```c++
#include "regular_expression.hpp"
```

Some advanced features have not been implemented yet, such as assertions and backreferences.

## Usage

Free functions are available:
```c++
using namespace rais::regex;

// Match the whole target with the pattern:
auto [errc, match] = regex::match("target", "pattern");

// Search for the first occurrence of the pattern in the target:
auto [errc, match] = regex::search("target", "pattern");

// Search for all occurrences of the pattern in the target:
auto [errc, matches] = regex::search_all("target", "pattern");

// Replace the specified count (default is unlimited) of matches of the pattern in the target:
std::string target = "target";
auto [errc, replaced_count] = regex::replace(target, "pattern", "replacement" /*, replace-count */);

/*
    where the type of 
        errc is rais::regex::error_category;
        match is std::vector<string_view_like>;
        matches is std::vector<std::vector<string_view_like>>;
        replaced_count is std::size_t
*/ 
```

## Requirements

- C++20 or later

