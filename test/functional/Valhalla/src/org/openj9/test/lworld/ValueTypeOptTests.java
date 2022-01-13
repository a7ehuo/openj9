package org.openj9.test.lworld;

import org.testng.Assert;
import static org.testng.Assert.*;
import org.testng.annotations.Test;
import org.testng.annotations.BeforeClass;


@Test(groups = { "level.sanity" })
public class ValueTypeOptTests {
	public primitive static class Point {
		public final double x, y;

		public Point(double x, double y) {
			this.x = x; this.y = y;
		}
	}

	public static class EscapeException extends RuntimeException {
		public Object escapingObject;

		public EscapeException(Object o) {
			escapingObject = o;
		}
	}

	public static double result = 0.0;
	public static Point[] arr = new Point[] { new Point(3.0, 4.0) };

	@Test(priority=1)
	static public void testEAOpportunity1() throws Throwable {
		result = 0.0;

		evalTestEA1();
		evalTestEA1();
		assertEquals(result, 1000.0);

		result = 0.0;
	}

	static private void evalTestEA1() {
		// Test situation where EA could apply to value p1, but must
		// allocate contiguously
		for (int i = 0; i < 100; i++) {
			Point p1 = new Point(1.0, 2.0);
			Point p2 = arr[0];

			Point p3;
			Point p4;

			if (i % 2 == 0) {
				p3 = p2;
				p4 = p1;
			} else {
				p3 = p1;
				p4 = p2;
			}
			result += p1.x + p2.y;
		}
	}

	@Test(priority=1)
	static public void testEAOpportunity2() throws Throwable {
		evalTestEA2();
		evalTestEA2();
	}

	public static Point testEA2Field;

	static private void evalTestEA2() {
		double x = 0.5; double y = 2.0;

		for (int i = 0; i < 100; i++) {
			Point p1 = new Point(x, y);
			double updatex = -x*y*x;
			double updatey = x*y*y;
			x = updatex;
			y = updatey;
                        if (Math.abs(p1.x*p1.y) != 1.0) testEA2Field = p1;
		}
	}

	@Test(priority=1)
	static public void testEAOpportunity3() throws Throwable {
	}

	@Test(priority=1)
	static public void testEAOpportunity4() throws Throwable {
	}
}
