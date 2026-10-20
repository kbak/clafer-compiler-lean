#!/usr/bin/env python3
"""Run every Python regression, failing on an empty suite or any skipped test."""
import unittest

suite = unittest.defaultTestLoader.discover('tests', pattern='test_*.py')
result = unittest.TextTestRunner(verbosity=2).run(suite)
raise SystemExit(0 if result.wasSuccessful() and result.testsRun and not result.skipped else 1)
