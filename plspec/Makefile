tests:
	swipl -s plspec_test.pl -g "run_tests,halt."

sicstusTests:
	sicstus -l plspec_test.pl --goal "plspec_test:run_tests,halt."

allTests: tests sicstusTests
