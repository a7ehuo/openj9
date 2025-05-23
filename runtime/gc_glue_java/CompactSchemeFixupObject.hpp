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
 
#ifndef COMPACTSCHEMEOBJECTFIXUP_HPP_
#define COMPACTSCHEMEOBJECTFIXUP_HPP_

#include "j9cfg.h"
#include "objectdescription.h"

#include "CompactScheme.hpp"
#include "GCExtensions.hpp"

#if JAVA_SPEC_VERSION >= 24
class GC_ContinuationSlotIterator;
#endif /* JAVA_SPEC_VERSION >= 24 */

class MM_CompactSchemeFixupObject {
public:
protected:
private:
	OMR_VM *_omrVM;
	MM_GCExtensions *_extensions;
	MM_CompactScheme *_compactScheme;
public:

	MMINLINE void doSlot(MM_EnvironmentBase *env, omrobjectptr_t fromObject, omrobjectptr_t *slotPtr);
#if JAVA_SPEC_VERSION >= 24
	void doContinuationSlot(MM_EnvironmentBase *env, omrobjectptr_t fromObject, omrobjectptr_t *slotPtr, GC_ContinuationSlotIterator *continuationSlotIterator);
#endif /* JAVA_SPEC_VERSION >= 24 */
	void doStackSlot(MM_EnvironmentBase *env, omrobjectptr_t fromObject, omrobjectptr_t *slotPtr, J9StackWalkState *walkState, const void *stackLocation);
	/**
	 * Perform fixup for a single object
	 * @param env[in] the current thread
	 * @param objectPtr pointer to object for fixup
	 */
	void fixupObject(MM_EnvironmentStandard *env, omrobjectptr_t objectPtr);

	static void verifyForwardingPtr(omrobjectptr_t objectPtr, omrobjectptr_t forwardingPtr);

	MM_CompactSchemeFixupObject(MM_EnvironmentBase* env, MM_CompactScheme *compactScheme) :
		_omrVM(env->getOmrVM()),
		_extensions(MM_GCExtensions::getExtensions(env)),
		_compactScheme(compactScheme)
	{}

protected:
private:
	/**
	 * Perform fixup for a mixed object
	 * @param objectPtr pointer to object for fixup
	 */
	void fixupMixedObject(omrobjectptr_t objectPtr);

	/**
	 * Perform fixup for an array object
	 * @param objectPtr pointer to object for fixup
	 */
	void fixupArrayObject(omrobjectptr_t objectPtr);

	/**
	 * Perform fixup for a flattened array object
	 * @param objectPtr pointer to object for fixup
	 */
	void fixupFlattenedArrayObject(omrobjectptr_t objectPtr);

	void fixupContinuationNativeSlots(MM_EnvironmentStandard *env, omrobjectptr_t objectPtr);
	void fixupContinuationObject(MM_EnvironmentStandard *env, omrobjectptr_t objectPtr);
	/**
	 * Called whenever a ownable synchronizer object is fixed up during compact. Places the object on the thread-specific buffer of gc work thread.
	 * @param env -- current thread environment
	 * @param object -- The object of type or subclass of java.util.concurrent.locks.AbstractOwnableSynchronizer.
	 */
	MMINLINE void addOwnableSynchronizerObjectInList(MM_EnvironmentBase *env, omrobjectptr_t objectPtr);

	/**
	 * Determine whether the object pointer is found within the heap proper.
	 * @return Boolean indicating if the object pointer is within the heap boundaries.
	 */
	MMINLINE bool isHeapObject(J9Object *objectPtr)
	{
		return (_extensions->heap->getHeapBase() <= (uint8_t *)objectPtr) && (_extensions->heap->getHeapTop() > (uint8_t *)objectPtr);
	}
};

typedef struct StackIteratorData4CompactSchemeFixupObject {
	MM_CompactSchemeFixupObject *compactSchemeFixupObject;
	MM_EnvironmentBase *env;
	J9Object *fromObject;
} StackIteratorData4CompactSchemeFixupObject;

#endif /* COMPACTSCHEMEOBJECTFIXUP_HPP_ */
