cmake_minimum_required (VERSION 3.0)
project (hvpspace)
set(NAME "hvpspace")

find_path(CMAKE_FOLDER NAMES cmake/emp-tool-config.cmake)
include(${CMAKE_FOLDER}/cmake/emp-base.cmake)

find_package(emp-zk REQUIRED)
include_directories(${EMP-ZK_INCLUDE_DIRS})
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CMAKE_C_FLAGS} -std=c++14")

#set(sources
  
#)
#add_library(${NAME} SHARED ${sources})

#install(DIRECTORY emp-zk DESTINATION include/)
#install(FILES cmake/emp-zk-config.cmake DESTINATION cmake/)
#install(TARGETS ${NAME} DESTINATION lib)

add_executable(test_solver "solver.cpp")
target_link_libraries(test_solver ${EMP-ZK_LIBRARIES})

#add_test(NAME ${folder}_${_name} COMMAND "./run" "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test_${folder}_${_name}" WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/")

#ENABLE_TESTING()
#ADD_SUBDIRECTORY(test)
