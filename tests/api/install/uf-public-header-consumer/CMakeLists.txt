cmake_minimum_required(VERSION 3.16)
project(stp_uf_public_header_consumer LANGUAGES CXX)

find_package(STP CONFIG REQUIRED)

add_executable(stp-uf-public-header-consumer main.cpp)
target_compile_features(stp-uf-public-header-consumer PRIVATE cxx_std_11)
target_include_directories(
  stp-uf-public-header-consumer PRIVATE "${STP_INSTALLED_INCLUDE_DIR}")
target_link_libraries(stp-uf-public-header-consumer PRIVATE stp)
