# Only set options and variables once by the first called deps.cmake file
if(NOT DEFINED DEPS_INITIALIZED)
    option(UPDATE_PYTHON_DEPS "Force update dependencies" OFF)
    option(DEPS_USE_VENV "Create a Python virtual environment and install dependencies locally" ON)
    option(UPDATE_DEPS "Update all of the dependencies, CPM packages and Python" OFF)

    # CPM variable used for downloaded packages location
    set(FETCHCONTENT_BASE_DIR ${CMAKE_CURRENT_LIST_DIR}/_deps CACHE INTERNAL "")
    # Set the venv location used by the venv.cmake files
    set(PYTHON_VENV_BASE_DIR ${CMAKE_CURRENT_LIST_DIR}/_deps CACHE INTERNAL "")
    # Flag the initialization
    set(DEPS_INITIALIZED TRUE CACHE INTERNAL "")
endif()

# Define CPM version to be downloaded
set(CPM_DOWNLOAD_VERSION 0.38.1)
# Include the CPM.cmake downloader
include(${CMAKE_CURRENT_LIST_DIR}/CPM.cmake)

CPMAddPackage(
    NAME tech_cells_generic
    GIT_TAG v0.2.13
    GIT_REPOSITORY "https://github.com/HEP-SoC/tech_cells_generic.git"
)
