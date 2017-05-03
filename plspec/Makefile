tests:
	swipl -s plspec_test.pl -g "run_tests,halt."

inference_tests:
	swipl -s plspec_inference.pl -g "run_tests,halt."

sicstusTests:
	sicstus -l plspec_test.pl --goal "run_tests,halt."

allTests: tests sicstusTests inference_tests
