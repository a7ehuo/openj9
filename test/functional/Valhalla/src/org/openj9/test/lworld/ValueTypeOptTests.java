/*******************************************************************************
 * Copyright IBM Corp. and others 2022
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
 * or the Apache License, Version 2.0 which accompanies this distribution and
 * is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following
 * Secondary Licenses when the conditions for such availability set
 * forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
 * General Public License, version 2 with the GNU Classpath
 * Exception [1] and GNU General Public License, version 2 with the
 * OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] https://openjdk.org/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0
 *******************************************************************************/
package org.openj9.test.lworld;

import org.testng.Assert;
import static org.testng.Assert.*;
import org.testng.annotations.Test;
import org.testng.annotations.BeforeClass;


@Test(groups = { "level.sanity" })
public class ValueTypeOptTests {
	// An ordinary (non-null-restricted) value class
	public static value class Pair {
		public final int x, y;

		public Pair(int x, int y) {
			this.x = x; this.y = y;
		}

		public Pair(Pair p) {
			this.x = p.x; this.y = p.y;
		}
	}

	public static class EscapeException extends RuntimeException {
		public Object escapingObject;

		public EscapeException(Object o) {
			escapingObject = o;
		}
	}

	public static int result = 0;
	public static Pair[] arr = new Pair[] { new Pair(3, 4) };

	@Test(priority=1)
	static public void testEAOpportunity1() throws Throwable {
		for (int i = 0; i < 10000; i++) {
			result = 0;
			for (int j = 0; j < 100; j++) {
				evalTestEA1a(j);
			}
			assertEquals(result, 500);

			result = 0;
			evalTestEA1b();
			assertEquals(result, 500);
		}
	}

	static private void evalTestEA1a(int iter) {
		// Test situation where EA could apply to value p1,
		// but might have to allocate contiguously
		Pair p1 = new Pair(1, 2);
		Pair p2 = arr[0];

		Pair p3;
		Pair p4;

		if (iter % 2 == 0) {
			p3 = p1;
			p4 = p2;
		} else {
			p3 = p2;
			p4 = p1;
		}


		if (result >= 0) {
			result += p3.x + p4.y;
		}
	}

	static private void evalTestEA1b() {
		for (int j = 0; j < 100; j++) {
			// Test situation where EA could apply to value p1,
			// but might have to allocate contiguously.  Also,
			// extra challenges for stack allocation in a loop
			Pair p1 = new Pair(1, 2);
			Pair p2 = arr[0];

			Pair p3;
			Pair p4;

			if (j % 2 == 0) {
				p3 = p1;
				p4 = p2;
			} else {
				p3 = p2;
				p4 = p1;
			}


			if (result >= 0) {
				result += p3.x + p4.y;
			}
		}
	}

	@Test(priority=1)
	static public void testEAOpportunity2() throws Throwable {
		for (int i = 0; i < 10000; i++) {
			result = 0;
			evalTestEA2();
			assertEquals(result, 200);
			assertEquals(testEA2Field, new Pair(0,0));
		}
	}

	public static Pair testEA2Field = new Pair(0,0);

	static private void evalTestEA2() {
		int x = 1; int y = 2;

		for (int i = 0; i < 100; i++) {
			Pair p1 = new Pair(x, y);
			int updatex = (x-y)*(x-y);
			int updatey = y*(y-x);
			x = updatex;
			y = updatey;
			if (p1.x*p1.y != 2) testEA2Field = p1;  // Looks like value might escape (but never actually does)

			result += x*y;
		}
	}

	@Test(priority=1)
	static public void testEAOpportunity3() throws Throwable {
		for (int i = 0; i < 1000; i++) {
			result = 0;
			evalTestEA3();
			assertEquals(result, 1000);
		}
	}

	static private void evalTestEA3() {
		for (int i = 0; i < 100; i++) {
			// Test potential stack allocation of array of value type
			Pair[] arr = new Pair[] {new Pair(1, 2), new Pair(3, 4)};
			for (int j = 0; j < arr.length; j++) {
				Pair val = arr[j%arr.length];
				result += val.x + val.y;
			}
		}
	}

	public static value class NestedPair {
		public final Pair p1;
		public final Pair p2;

		public NestedPair(int i, int j, int m, int n) {
			this.p1 = new Pair(i, j);
			this.p2 = new Pair(m, n);
		}

		public NestedPair(Pair p1, Pair p2) {
			this.p1 = new Pair(p1);
			this.p2 = new Pair(p2);
		}
	}

	public static NestedPair[] nestedarr = new NestedPair[] { new NestedPair(7, 8, 9, 10) };

	@Test(priority=1)
	static public void testEAOpportunity7() throws Throwable {
		for (int i = 0; i < 10000; i++) {
			result = 0;
			for (int j = 0; j < 100; j++) {
				evalTestEA7a(j);
			}
			assertEquals(result, 1100);

			result = 0;
			evalTestEA7b();
			assertEquals(result, 1100);
		}
	}

	static private void evalTestEA7a(int iter) {
		// Test situation where EA could apply to value p1,
		// but might have to allocate contiguously
		NestedPair p1 = new NestedPair(1, 2, 3, 4);
		NestedPair p2 = nestedarr[0];

		NestedPair p3;
		NestedPair p4;

		if (iter % 2 == 0) {
			p3 = p2;
			p4 = p1;
		} else {
			p3 = p1;
			p4 = p2;
		}
		result += p3.p1.x + p4.p2.y;
	}

	static private void evalTestEA7b() {
		for (int j = 0; j < 100; j++) {
			// Test situation where EA could apply to value p1,
			// but might have to allocate contiguously.  Also,
			// extra challenges for stack allocation in a loop
			NestedPair p1 = new NestedPair(1, 2, 3, 4);
			NestedPair p2 = nestedarr[0];

			NestedPair p3;
			NestedPair p4;

			if (j % 2 == 0) {
				p3 = p1;
				p4 = p2;
			} else {
				p3 = p2;
				p4 = p1;
			}

			result += p3.p1.x + p4.p2.y;
		}
	}
	@Test(priority=1)
	static public void testEAOpportunity8() throws Throwable {
		for (int i = 0; i < 10000; i++) {
			result = 0;
			evalTestEA8();
			assertEquals(result, 2400);
			assertEquals(testEA8Field, new NestedPair(0,0,0,0));
		}
	}

	public static NestedPair testEA8Field = new NestedPair(0,0,0,0);

	static private void evalTestEA8() {
		int x = 1; int y = 2; int z = 3; int w = 4;

		for (int i = 0; i < 100; i++) {
			NestedPair p = new NestedPair(x, y, z, w);
			int updatex = (x-y)*(x-y);
			int updatey = y*(y-x);
			int updatez = (z-w)*(z-w)*z;
			int updatew = w*(w-z);
			x = updatex;
			y = updatey;
			z = updatez;
			w = updatew;
			if (p.p1.x*p.p1.y*p.p2.x*p.p2.y != 24) testEA8Field = p;  // Looks like value might escape (but never actually does)

			result += x*y*z*w;
		}
	}

	@Test(priority=1)
	static public void testEAOpportunity9() throws Throwable {
		for (int i = 0; i < 1000; i++) {
			result = 0;
			evalTestEA9();
			assertEquals(result, 1800);
		}
	}

	static private void evalTestEA9() {
		for (int i = 0; i < 100; i++) {
			// Test potential stack allocation of array of value type
			NestedPair[] arr = new NestedPair[] {new NestedPair(1, 2, 3, 4), new NestedPair(5, 6, 7, 8)};
			for (int j = 0; j < arr.length; j++) {
				NestedPair val = arr[j%arr.length];
				result += val.p1.x + val.p2.y;
			}
		}
	}

	public static int sval13 = 0;
	public static Pair escape13 = new Pair(0,0);

	@Test(priority=1)
	static public void testEAOpportunity13() throws Throwable {
		result = 0;
		for (int i = 0; i < 100000; i++) {
			evalTestEA13(i*sval13);
		}
		assertEquals(result, 500000);
		assertEquals(escape13, new Pair(0,0));

		evalTestEA13(sval13+99);
		assertEquals(result, 500000);
		assertEquals(escape13, new Pair(1,2));
	}

	static private void evalTestEA13(int i) {
		// Test cold block escape for value object
		Pair p = new Pair(1, 2);

		try {
			result += p.x + arr[i].y;
		} catch (ArrayIndexOutOfBoundsException aioobe) {
			escape13 = p;
		}
	}

	public static int sval15 = 0;
	public static NestedPair escape15 = new NestedPair(0,0,0,0);

	@Test(priority=1)
	static public void testEAOpportunity15() throws Throwable {
		result = 0;
		for (int i = 0; i < 100000; i++) {
			evalTestEA15(i*sval15);
		}
		assertEquals(result, 1100000);
		assertEquals(escape15, new NestedPair(0,0,0,0));

		evalTestEA15(sval15+99);
		assertEquals(result, 1100000);
		assertEquals(escape15, new NestedPair(1,2,3,4));
	}

	static private void evalTestEA15(int i) {
		// Test cold block escape for nested value objects
		NestedPair p = new NestedPair(1, 2, 3, 4);

		try {
			result += p.p1.x + nestedarr[i].p2.y;
		} catch (ArrayIndexOutOfBoundsException aioobe) {
			escape15 = p;
		}
	}
}
