import doctest
import inspect

import automata


def test_doctests():
    """Runs the examples in the docstrings of all classes of the package."""
    finder = doctest.DocTestFinder()
    runner = doctest.DocTestRunner()
    classes = [c for _, c in inspect.getmembers(automata, inspect.isclass) if c.__module__.startswith("automata")]
    for cls in classes:
        for test in finder.find(cls, cls.__name__, globs=dict(vars(automata))):
            runner.run(test)
    results = runner.summarize(verbose=False)
    assert results.attempted >= 20 and results.failed == 0
