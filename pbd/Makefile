default : slow

slow :
	scalac -feature -deprecation -unchecked -d target/scala-2.10/classes src/main/scala/pbd/{*.scala,*/*.scala}

fast :
	fsc -feature -deprecation -unchecked -d target/scala-2.10/classes src/main/scala/pbd/{*.scala,*/*.scala}
