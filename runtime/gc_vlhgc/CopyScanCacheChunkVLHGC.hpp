
/*******************************************************************************
 * Copyright IBM Corp. and others 1991
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

/**
 * @file
 * @ingroup GC_Modron_Standard
 */

#if !defined(COPYSCANCACHECHUNKVLHGC_HPP_)
#define COPYSCANCACHECHUNKVLHGC_HPP_

#include "BaseVirtual.hpp"
#include "EnvironmentVLHGC.hpp" 

class MM_CopyScanCacheVLHGC;

/**
 * @todo Provide class documentation
 * @ingroup GC_Modron_Standard
 */
class MM_CopyScanCacheChunkVLHGC : public MM_BaseVirtual
{
private:
	MM_CopyScanCacheVLHGC *_baseCache;
	MM_CopyScanCacheChunkVLHGC *_nextChunk;
public:

	MMINLINE MM_CopyScanCacheVLHGC *getBase() const { return _baseCache; }
	MMINLINE MM_CopyScanCacheChunkVLHGC *getNext() const { return _nextChunk; }
	MMINLINE void setNext(MM_CopyScanCacheChunkVLHGC *newNext) { _nextChunk = newNext; }
	
	static MM_CopyScanCacheChunkVLHGC *newInstance(MM_EnvironmentVLHGC *env, uintptr_t cacheEntryCount, MM_CopyScanCacheVLHGC **tailCacheAddr, MM_CopyScanCacheChunkVLHGC *nextChunk);
	virtual void kill(MM_EnvironmentVLHGC *env);
	bool initialize(MM_EnvironmentVLHGC *env, uintptr_t cacheEntryCount, MM_CopyScanCacheVLHGC **tailCacheAddr, MM_CopyScanCacheChunkVLHGC *nextChunk);
	virtual void tearDown(MM_EnvironmentVLHGC *env);

	/**
	 * Create a CopyScanCacheChunk object.
	 */
	MM_CopyScanCacheChunkVLHGC() :
		MM_BaseVirtual(),
		_baseCache(NULL),
		_nextChunk(NULL)
	{
		_typeId = __FUNCTION__;
	};
	
};

#endif /* COPYSCANCACHECHUNKVLHGC_HPP_ */

