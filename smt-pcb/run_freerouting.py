#!/usr/bin/env python2

import subprocess
import argparse
import os
import os.path

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--dsn')
    parser.add_argument('--route_dir')
    args = parser.parse_args()

    # run FreeRouting in the correct directory
    args.route_dir = os.path.expanduser(args.route_dir)
    args.route_dir = os.path.abspath(args.route_dir)
    subprocess.Popen(['java', '-jar', 'FreeRouter.jar'], cwd=args.route_dir)

if __name__ == '__main__':
    main()
