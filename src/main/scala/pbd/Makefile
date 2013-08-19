default: slow testrule

slow:
	echo "Building..."
	mkdir -p classes
	scalac -deprecation -unchecked -d classes *.scala */*.scala

fast:
	echo "Building..."
	mkdir -p classes
	fsc -deprecation -unchecked -d classes *.scala */*.scala

clean:
	rm -rf classes
	fsc -shutdown


testrule:
	echo "Running tests"
	# these are essentially crash tests at the moment, if the don't crash, we assume they work... :(
	scala -cp classes graphprog.test.TestCompiler
	scala -cp classes graphprog.test.TestExecution

