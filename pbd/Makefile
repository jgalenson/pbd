default : slow

slow :
	mkdir -p target/scala-2.10/classes
	scalac -feature -deprecation -unchecked -d target/scala-2.10/classes src/main/scala/pbd/{*.scala,*/*.scala}

fast :
	mkdir -p target/scala-2.10/classes
	fsc -feature -deprecation -unchecked -d target/scala-2.10/classes src/main/scala/pbd/{*.scala,*/*.scala}
