
# Regex  

This c++ project implements a simple regular expression engine for text manipulation.

This is a header-only project.  

## Getting Started

- clone this repository, and set the `./include/` path to compiler include search path;
- include main header file: 
```c++
#include "regular_expression.hpp"
```

Some advanced features are not been implemented yet, such as assertions and backward reference;

## Usage

Free functions are available:
```c++

using namespace rais::regex;

// Match the whole target with pattern:
auto [errc, match] = regex::match("target", "pattern");

// Search the first occurance of pattern in target:
auto [errc, match] = regex::search("target", "pattern");

// Search all of the occurance of pattern in target:
auto [errc, matches] = regex::search_all("target", "pattern");

// Replace the appointed count(default is unlimited) of matches of pattern in target:
std::string target = "target";
auto [errc, replaced_count] = regex::replace(target, "pattern", "replacement" /*, replace-count */);

/*
    where type of 
        errc is rais::regex::error_category;
        match is std::vector<string_view_like>;
        matches is std::vector<std::vector<string_view_like>>;
        replaced_count is std::size_t
*/ 


```

## Requirements

- C++20 or later