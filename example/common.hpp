#pragma once

// some common utils for testing

#include <limits>
#include <string>
#include <format>
#include <utility>
#include <iostream>
#include <iterator>
#include <string_view>

#include "../include/regular_expression.hpp"

template <typename... Args>
void print(std::format_string<Args...> format, Args&&... args) {
    std::cout << std::format(format, std::forward<Args>(args)...);
} 
template <typename... Args>
void println(std::format_string<Args...> format, Args&&... args) {
    print(format, std::forward<Args>(args)...);
    print("\n");
}
