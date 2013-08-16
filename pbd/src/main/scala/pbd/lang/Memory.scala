package pbd.lang

import scala.collection.mutable.{ Map => MMap, HashMap => MHashMap, Stack }
import AST._

/**
 * Memory of a running program.
 */
class Memory(val mem: Stack[MMap[String, Value]]) extends Serializable {

  import Memory._

  // Constructors.
  def this(m: MMap[String, Value]) = this(Stack[MMap[String, Value]](m))
  def this(l: TraversableOnce[(String, Value)]) = this(MHashMap.empty ++ l)
  def this() = this(MHashMap[String, Value]())
  
  /**
   * Adds a given mapping to memory.
   */
  def +=(kv: (String, Value)): Memory = {
    mem.find{ _ contains kv._1 } match {
      case Some(m) => m(kv._1) = kv._2
      case None => mem.top += kv
    }
    this
  }

  /**
   * Gets the value of the given variable.
   */
  def apply(key: String): Value = mem.find{ _ contains key }.get(key)

  /**
   * Checks whether the given variable is defined.
   */
  def contains(key: String): Boolean = mem.find{ _ contains key}.isDefined

  /**
   * Enters/exits a scope.
   */
  protected[pbd] def enterScope(): Unit = mem.push(MMap[String, Value]())
  protected[pbd] def exitScope(): Unit = mem.pop

  /**
   * Gets all of the variables.
   */
  def keys: Seq[String] = mem flatMap { _.keys }
  
  /**
   * Makes a clone of this memory.
   */
  override def clone: Memory = new Memory(cloneHelper(mem, Stack[MMap[String, Value]]()))
  
  /**
   * Makes this memory a clone of the other memory.
   */
  def cloneFrom(other: Memory) {
    mem.clear
    cloneHelper(other.mem, mem)
  }

  /**
   * Gets all objects and arrays.
   */
  def getObjectsAndArrays(): (MMap[Int, Object], MMap[Int, ArrayValue]) = getObjectsAndArraysHelper(mem)

  /**
   * Gets the object/array with the given id.
   */
  def getObject(id: Int): Option[Object] = getObjectsAndArraysHelper(mem)._1.get(id)  // TODO-optimization: We could speed this (and getArray) up by not calling getObjectsAndArrays() and constructing the whole maps.
  def getArray(id: Int): Option[ArrayValue] = getObjectsAndArraysHelper(mem)._2.get(id)
  
  // Converts the memory.
  def toIterator: Iterator[(String, Value)] = mem.foldLeft(Iterator.apply[(String, Value)]()){ (acc, cur) => acc ++ cur.toIterator }
  def toMap: Map[String, Value] = toIterator.toMap
  
  override def equals(o: Any) = o match { case o: Memory => ASTUtils.memoriesAreEqual(this, o) case _ => false }
  override def hashCode: Int = mem.hashCode
  
  override def toString: String = (new Printer(Map.empty, true)).stringOfMemory(this)
  
}

object Memory {

  /**
   * Clone the given oldMemory into the given newMemory.
   */
  private def cloneHelper(oldMemory: Stack[MMap[String, Value]], newMemory: Stack[MMap[String, Value]]): Stack[MMap[String, Value]] = {
    val (objects, arrays) = getObjectsAndArraysHelper(oldMemory)
    val clonedObjects = MHashMap.empty ++ (objects mapValues { o => Object(o.id, o.typ, new MHashMap[String, Value]) })  // Note that this needs to be a mutable map not an immutable map or updates to its fields do not stick
    val clonedArrays = MHashMap.empty ++ (arrays mapValues { a => ArrayValue(a.id, new Array[Value](a.array.length), a.elemType) })
    def myclone(v: Value): Value = v match {
      case ArrayValue(id, _, _) => clonedArrays(id)
      case Object(id, _, _) => clonedObjects(id)
      case _ => v
    }
    clonedObjects.values foreach { clone => clone.fields ++= objects(clone.id).fields.map { t => (t._1 -> myclone(t._2)) } }
    clonedArrays.values.foreach{ clone => for (i <- 0 until clone.array.length) clone.array(i) = myclone(arrays(clone.id).array(i)) }
    oldMemory.reverse.foreach { m => newMemory push (MMap.empty ++ m.mapValues(myclone)) }
    newMemory
  }

  /**
   * Gets the objects and arrays of a given memory.
   */
  private def getObjectsAndArraysHelper(mem: Stack[MMap[String, Value]]): (MMap[Int, Object], MMap[Int, ArrayValue]) = {
    val objects = new MHashMap[Int, Object]
    val arrays = new MHashMap[Int, ArrayValue]
    def getObjectAndArray(v: Value): Unit = v match {
      case a @ ArrayValue(id, array, _) =>
	if (!arrays.contains(id)) {
	  arrays += (id -> a)
	  getObjectsAndArrays(array)
	}/* else
	  assert(a.eq(arrays(id)) && !objects.contains(id), a + " " + { if (a.eq(arrays(id))) objects(id) else arrays(id) } + " in " + (new Printer(Map.empty, true)).stringOfMemory(new Memory(mem)))*/
      case o @ Object(id, _, fields) =>
	if (!objects.contains(id)) {
	  objects += (id -> o)
	  getObjectsAndArrays(fields.values)
	}/* else
	  assert(o.eq(objects(id)) && !arrays.contains(id), o + " " + { if (o.eq(objects(id))) arrays(id) else objects(id) } + " in " + (new Printer(Map.empty, true)).stringOfMemory(new Memory(mem)))*/
      case _ => ()
    }
    def getObjectsAndArrays(values: Iterable[Value]) = values foreach getObjectAndArray
    getObjectsAndArrays(mem flatMap { _.values })
    (objects, arrays)
  }

}
