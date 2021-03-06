package pbd

object Utils {

  import scala.util.Random.nextInt

  /**
   * An exception that is faser than a normal one since it does not
   * need to fill in the stack trace.
   */
  trait FastException extends RuntimeException {
    override def fillInStackTrace: Throwable = this
  }

  /**
   * Converts an iterable into a string.
   */
  def iterableToString[T](x: Iterable[T], sep: String, toStringFn: T => String = (t: T) => t.toString, init: String = ""): String = x.foldLeft(init)((acc, cur) => acc + (if (acc == init) "" else sep) + toStringFn(cur))

  /**
   * Ensures that the given property holds over the given iterable.
   */
  def holdsOverIterable[T](x: Iterable[T], f: (T, T) => Boolean): Boolean = x.size == 1 || x.sliding(2).forall{ l => f(l.head, l.tail.head) }

  /**
   * Generates a random number in [min, max].
   */
  def nextBoundedInt(min: Int, max: Int): Int = nextInt(max - min + 1) + min

  /**
   * Picks a random element.
   */
  def randomElement[T](s: Seq[T]): T = s(nextInt(s.size))

  /**
   * Chooses either the singular or plural form.
   */
  def pluralize(singular: String, plural: String, count: Int): String = if (count == 1) singular else plural

  /**
   * Executes the given function with the given timeout.
   */
  trait ExecutionResult[+T]
  case class NormalResult[T](val result: T) extends ExecutionResult[T]
  case class ExceptionThrown(val e: Throwable) extends ExecutionResult[Nothing]
  case object Timeout extends ExecutionResult[Nothing]
  def executeWithTimeout[T](f: => T, timeout: Long): ExecutionResult[T] = {
    import java.util.concurrent.{Executors, Callable, TimeUnit, TimeoutException, ExecutionException}
    val executor = Executors.newCachedThreadPool()
    val task = executor.submit(new Callable[T](){ def call() = f })
    try {
      NormalResult(task.get(timeout, TimeUnit.MILLISECONDS))
    } catch {
      case _: TimeoutException | _: pbd.lang.Executor.InterruptedException => Timeout
      case e: ExecutionException => ExceptionThrown(e.getCause)
    } finally {
      task.cancel(true)
      executor.shutdownNow()
    }
  }

  /**
   * Rounds the given double to the given number of places.
   */
  def round(n: Double, numPlaces: Int): Double = {
    val p = math.pow(10, numPlaces)
    (n * p).toInt / p.toDouble
  }

  /**
   * Ensures that the given list is a singleton and returns its only element.
   */
  def singleton[T](l: List[T]): T = l match {
    case x :: Nil => x
    case _ => throw new RuntimeException("List " + l + " is not a singleton.")
  }

  /**
   * Wrappers for the SwingUtilities/SwingWorker invoke* methods that use nice lambdas.
   */
  def invokeAndWait(f: => Unit) = javax.swing.SwingUtilities.invokeAndWait(new Runnable() {
    def run() = f
  })
  def invokeLater(f: => Unit) = javax.swing.SwingUtilities.invokeLater(new Runnable() {
    def run() = f
  })
  def invokeOffSwingThread[T,V](workFn: => T, doneFn: T => Unit) = (new javax.swing.SwingWorker[T, V]() {
    override def doInBackground(): T =
      try {
	  workFn
      } catch {
	case e: Throwable =>  // If this thread throws an exception, we must catch and rethrow it or we will silently miss the error and hang.
	  e.printStackTrace()
	  throw e
      }
    override def done() = doneFn(get())
  }).execute()

  /**
   * Helper methods to setup and add controls such as menu items and buttons.
   */
  import javax.swing.AbstractButton
  import java.awt.Container
  import java.awt.event.{ ActionEvent, ActionListener }
  def setupControl[T <: AbstractButton](control: T, parent: Container, mnemonic: Int): T = setupControlImpl(control, parent, None, Some(mnemonic))
  def setupControl[T <: AbstractButton](control: T, parent: Container, action: ActionEvent => Unit, mnemonic: Int): T = setupControlImpl(control, parent, Some(action), Some(mnemonic))
  def setupControl[T <: AbstractButton](control: T, parent: Container, action: ActionEvent => Unit): T = setupControlImpl(control, parent, Some(action), None)
  private def setupControlImpl[T <: AbstractButton](control: T, parent: Container, action: Option[ActionEvent => Unit], mnemonic: Option[Int]): T = {
    mnemonic.foreach{ mnemonic => control.setMnemonic(mnemonic) }
    action foreach { action => control.addActionListener(new ActionListener() {
      def actionPerformed(e: ActionEvent) = action(e)
    }) }
    parent.add(control)
    control
  }

  class NotImplementedError extends Error
  def TODO: Nothing = throw new NotImplementedError

  /**
   * Times the execution of the given statement.
   */
  def time[T](f: => T): T = {
    val startTime = System.currentTimeMillis()
    val result = f
    println((System.currentTimeMillis - startTime))
    result
  }

}
