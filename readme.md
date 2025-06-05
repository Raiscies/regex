
# Regex  

This c++ project implements a simple regular expression engine for text manipulation.

## Getting Started

- clone this repository, and set the ./include/ path to compiler include search path;
- include main header file: 
```c++
#include "regular_expression.hpp"
```
## Supported Features

- basic regular expression operators such as kleene closure`*` and positive closure`+` and so on;

Some features are not been implemented yet, such as assertions and backward reference;

## Usage

Some free functions are available:
```c++

using namespace rais::regex;

// Match:
auto [errc, match] = regex::match("target", "pattern");

// Search:
auto [errc, match] = regex::search("target", "pattern");

// Search All:
auto [errc, matches] = regex::search_all("target", "pattern");

// Replace:
std::string target = "target";
auto [errc, matches] = regex::replace(target, "pattern"/*, replace-count */);

/*
    where type of 
        errc is rais::regex::error_category;
        match is std::vector<string_view_like>;
        matches is std::vector<std::vector<string_view_like>>;
*/ 


```

## Requirements

- C++20 or later