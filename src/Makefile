default: build testrule


build:
	echo "Building..."
	mkdir -p classes
	fsc -d classes *.scala */*.scala

clean:
	rm -rf classes
	fsc -shutdown


testrule:
	echo "Running tests"
	scala -cp classes graphprog.test.TestCompiler
