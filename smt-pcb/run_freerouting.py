#!/usr/bin/env python2

import subprocess
import argparse
import os
import os.path
import time

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--dsn')
    parser.add_argument('--route_dir')
    args = parser.parse_args()

    # find the DSN file
    args.dsn = os.path.expanduser(args.dsn)
    args.dsn = os.path.abspath(args.dsn)

    # run FreeRouting in the correct directory
    args.route_dir = os.path.expanduser(args.route_dir)
    args.route_dir = os.path.abspath(args.route_dir)
    jar_cmd = ['java', '-jar', 'FreeRouter.jar', 
               '-de', args.dsn,
               '-di', os.path.dirname(args.dsn)]
    print jar_cmd
    proc = subprocess.Popen(jar_cmd, cwd=args.route_dir)
    proc.wait()

if __name__ == '__main__':
    main()
