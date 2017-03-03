#!/bin/bash

source ../venv/bin/activate
python smt_place.py $1
deactivate

