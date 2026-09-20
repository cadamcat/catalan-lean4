#!/opt/lean-4.33.1/bin/python3-audit
import os
import sys
os.environ.update(LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false', MATHLIB_NO_CACHE_ON_UPDATE='1', LAKE_CACHE_DIR='', LEAN_NUM_THREADS='16')
os.execv('/opt/lean-4.33.1/bin/lake-original', ['lake', '--no-cache', *sys.argv[1:]])
