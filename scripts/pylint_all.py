#! /usr/bin/env python3

"""
Performs pylint on all python files in the project repo's test directory recursively.

This script is meant to be run from the CI but can also be easily in local dev environment.
"""

from os import path, walk, system
from sys import exit as brexit

PROJECT_ROOT = path.dirname(path.realpath(__file__))
PYLINT_RCFILE = "{}/pylintrc".format(PROJECT_ROOT)

SGR_INFO = "\033[1;32m"
SGR_CLEAR = "\033[0m"

def pylint_all_filenames(rootdirs):
    """ Performs pylint on all python files within given root directory (recursively).  """
    filenames = []
    for rootdir in rootdirs:
        for rootpath, _, filenames_w in walk(rootdir):
            for filename in filenames_w:
                if filename.endswith('.py'):
                    filenames.append(path.join(rootpath, filename))

    failed = []
    for filename in filenames:
        cmdline = "pylint --rcfile=\"{}\" \"{}\"".format(PYLINT_RCFILE, filename)
        print("{}Running pylint on file: {}{}".format(SGR_INFO, filename, SGR_CLEAR))
        exit_code = system(cmdline)
        if exit_code != 0:
            failed.append(filename)

    return len(failed), len(filenames)

def main():
    """" Collects all python script root dirs and runs pylint on them. """
    failed_count, total_count = pylint_all_filenames([
        path.abspath(path.dirname(__file__) + "/../scripts"),
        path.abspath(path.dirname(__file__) + "/../test")])
    if failed_count != 0:
        brexit("pylint failed on {}/{} files.".format(failed_count, total_count))
    else:
        print("Successfully tested {} files.".format(total_count))

if __name__ == "__main__":
    main()
