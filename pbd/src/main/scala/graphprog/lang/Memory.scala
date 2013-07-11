package graphprog.lang

import scala.collection.mutable.{ Map => MMap, HashMap => MHashMap, Stack }
import AST._

class Memory(val mem: Stack[MMap[String, Value]]) extends Serializable {

  import Memory._

  def this(m: MMap[String, Value]) = this(Stack[MMap[String, Value]](m))
  def this(l: TraversableOnce[(String, Value)]) = this(MHashMap.empty ++ l)
  def this() = this(MHashMap[String, Value]())
  
  def +=(kv: (String, Value)): Memory = {
    mem.find{ _ contains kv._1 } match {
      case Some(m) => m(kv._1) = kv._2
      case None => mem.top += kv
    }
    this
  }
  def apply(key: String): Value = mem.find{ _ contains key }.get(key)
  def contains(key: String): Boolean = mem.find{ _ contains key}.isDefined
  protected[graphprog] def enterScope: Unit = mem.push(MMap[String, Value]())
  protected[graphprog] def exitScope: Unit = mem.pop
  def keys: Iterable[String] = mem flatMap { _.keys }
  
  override def clone: Memory = new Memory(cloneHelper(mem, Stack[MMap[String, Value]]()))
  def cloneFrom(other: Memory) {
    mem.clear
    cloneHelper(other.mem, mem)
  }
  private def cloneHelper(oldMemory: Stack[MMap[String, Value]], newMemory: Stack[MMap[String, Value]]): Stack[MMap[String, Value]] = {
    val (objects, arrays) = getObjectsAndArraysHelper(oldMemory)
    val clonedObjects = MHashMap.empty ++ (objects mapValues { o => Object(o.id, o.typ, new MHashMap[String, Value]) })  // Note that this needs to be a mutable map not an immutable map or updates to its fields do not stick
    val clonedArrays = MHashMap.empty ++ (arrays mapValues { a => IntArray(a.id, a.array.clone) })
    def myclone(v: Value): Value = v match {
      case IntArray(id, _) => clonedArrays(id)
      case Object(id, _, _) => clonedObjects(id)
      case _ => v
    }
    clonedObjects.values foreach { clone => clone.fields ++= objects(clone.id).fields.map { t => (t._1 -> myclone(t._2)) } }
    oldMemory.reverse.foreach { m => newMemory push (MMap.empty ++ m.mapValues(myclone)) }
    newMemory
  }
  def getObjectsAndArrays(): (MMap[Int, Object], MMap[Int, IntArray]) = getObjectsAndArraysHelper(mem)
  
  def getObject(id: Int): Option[Object] = getObjectsAndArraysHelper(mem)._1.get(id)  // TODO-optimization: We could speed this (and getArray) up by not calling getObjectsAndArrays() and constructing the whole maps.
  def getArray(id: Int): Option[IntArray] = getObjectsAndArraysHelper(mem)._2.get(id)
  
  def toIterator: Iterator[(String, Value)] = mem.foldLeft(Iterator.apply[(String, Value)]()){ (acc, cur) => acc ++ cur.toIterator }
  def toMap: Map[String, Value] = toIterator.toMap
  
  override def equals(o: Any) = o match { case o: Memory => ASTUtils.memoriesAreEqual(this, o) case _ => false }
  override def hashCode: Int = mem.hashCode
  
  override def toString: String = (new Printer(Map.empty, true)).stringOfMemory(this)
  
}

object Memory {

  private def getObjectsAndArraysHelper(mem: Stack[MMap[String, Value]]): (MMap[Int, Object], MMap[Int, IntArray]) = {
    val objects = new MHashMap[Int, Object]
    val arrays = new MHashMap[Int, IntArray]
    def getObjectAndArray(v: Value): Unit = v match {
      case a: IntArray => arrays += (a.id -> a)
      case o @ Object(id, _, fields) =>
	if (!objects.contains(id)) {
	  objects += (id -> o)
	  getObjectsAndArrays(fields.values)
	}
      case _ => ()
    }
    def getObjectsAndArrays(values: Iterable[Value]) = values foreach getObjectAndArray
    getObjectsAndArrays(mem flatMap { _.values })
    (objects, arrays)
  }

}
