/*******************************************************************************
 * Copyright IBM Corp. and others 2000
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

#ifndef SYMBOL_VALIDATION_MANAGER_INCL
#define SYMBOL_VALIDATION_MANAGER_INCL

#include <algorithm>
#include <map>
#include <set>
#include <vector>
#include <stddef.h>
#include <stdint.h>
#include "env/jittypes.h"
#include "j9.h"
#include "j9nonbuilder.h"
#include "infra/TRlist.hpp"
#include "env/TRMemory.hpp"
#include "env/VMJ9.h"
#include "exceptions/AOTFailure.hpp"
#include "runtime/J9Runtime.hpp"

#if defined(J9VM_OPT_JITSERVER)
class ClientSessionData;
#endif /* defined(J9VM_OPT_JITSERVER) */
class AOTCacheClassChainRecord;
class AOTCacheWellKnownClassesRecord;


#define SVM_ASSERT_LOCATION_INNER(line) __FILE__ ":" #line
#define SVM_ASSERT_LOCATION(line) SVM_ASSERT_LOCATION_INNER(line)

#define SVM_ASSERT_IMPL(assertName, nonfatal, condition, condStr, format, ...)                  \
   do                                                                                           \
      {                                                                                         \
      if (!(condition))                                                                         \
         {                                                                                      \
         if (!(nonfatal) && ::TR::SymbolValidationManager::assertionsAreFatal())                \
            ::TR::fatal_assertion(__FILE__, __LINE__, condStr, "" format "", ##__VA_ARGS__);    \
         else                                                                                   \
            traceMsg(::TR::comp(), "" format "\n", ##__VA_ARGS__);                              \
                                                                                                \
         ::TR::comp()->failCompilation< ::J9::AOTSymbolValidationManagerFailure>(               \
            SVM_ASSERT_LOCATION(__LINE__) ": " assertName " failed: " condStr);                 \
         }                                                                                      \
      }                                                                                         \
   while (false)

// For logic errors. This is a fatal assertion in debug mode or when
// TR_svmAssertionsAreFatal is set in the environment. Otherwise it fails safe
// by bailing out of the current compilation or AOT load.
#define SVM_ASSERT(condition, format, ...) \
   SVM_ASSERT_IMPL("SVM_ASSERT", false, condition, #condition, format, ##__VA_ARGS__)

// For unhandled situations that are not necessarily a logic error, e.g.
// exceeding limits. This is never fatal; it always bails out of the current
// compilation or AOT load. Failure should be possible but very rare.
#define SVM_ASSERT_NONFATAL(condition, format, ...) \
   SVM_ASSERT_IMPL("SVM_ASSERT_NONFATAL", true, condition, #condition, format, ##__VA_ARGS__)

#define SVM_ASSERT_ALREADY_VALIDATED(svm, value)        \
   do                                                    \
      {                                                  \
      void *_0value = (value);                         \
      SVM_ASSERT_IMPL(                                   \
         "SVM_ASSERT_ALREADY_VALIDATED",                 \
         false,                                          \
         (svm)->isAlreadyValidated(_0value),            \
         "isAlreadyValidated(" #value ")",              \
         "%s %p should have already been validated",     \
         #value,                                        \
         _0value);                                      \
      }                                                  \
   while (false)

namespace TR {

struct SymbolValidationRecord
   {
   SymbolValidationRecord(TR_ExternalRelocationTargetKind kind)
      : _kind(kind)
      {}

   bool isEqual(SymbolValidationRecord *other)
      {
      return !isLessThan(other) && !other->isLessThan(this);
      }

   bool isLessThan(SymbolValidationRecord *other)
      {
      if (_kind < other->_kind)
         return true;
      else if (_kind > other->_kind)
         return false;
      else
         return isLessThanWithinKind(other);
      }

   virtual void printFields() = 0;

   virtual bool isClassValidationRecord() { return false; }

   TR_ExternalRelocationTargetKind _kind;

protected:
   virtual bool isLessThanWithinKind(SymbolValidationRecord *other) = 0;

   template <typename T>
   static T *downcast(T *that, SymbolValidationRecord *record)
      {
      TR_ASSERT(record->_kind == that->_kind, "unexpected SVM record comparison");
      return static_cast<T*>(record);
      }
   };

// Comparison for STL
struct LessSymbolValidationRecord
   {
   bool operator()(SymbolValidationRecord *a, SymbolValidationRecord *b) const
      {
      return a->isLessThan(b);
      }
   };

struct ClassValidationRecord : public SymbolValidationRecord
   {
   ClassValidationRecord(TR_ExternalRelocationTargetKind kind)
      : SymbolValidationRecord(kind)
      {}

   virtual bool isClassValidationRecord() { return true; }
   };

// A class validation where the class chain provides data that is used to find
// the class (e.g. its name). It can be advantageous to use a class chain even
// when it is not required for the validation at hand, since each class needs a
// class chain validation at some point. By including one in ClassByNameRecord
// (for example), it's possible to eliminate the separate ClassChainRecord that
// would otherwise be required.
struct ClassValidationRecordWithChain : public ClassValidationRecord
   {
   ClassValidationRecordWithChain(TR_ExternalRelocationTargetKind kind, TR_OpaqueClassBlock *clazz)
      : ClassValidationRecord(kind), _class(clazz), _classChainOffset(TR_SharedCache::INVALID_CLASS_CHAIN_OFFSET)
      {
#if defined(J9VM_OPT_JITSERVER)
      _aotCacheClassChainRecord = NULL;
#endif /* defined(J9VM_OPT_JITSERVER) */
      }

   virtual void printFields();

#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheClassChainRecord *getAOTCacheClassChainRecord() const { return _aotCacheClassChainRecord; }
#else /* defined(J9VM_OPT_JITSERVER) */
   const AOTCacheClassChainRecord *getAOTCacheClassChainRecord() const { return NULL; }
#endif /* defined(J9VM_OPT_JITSERVER) */

   TR_OpaqueClassBlock *_class;
   uintptr_t _classChainOffset;
#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheClassChainRecord *_aotCacheClassChainRecord;
#endif /* defined(J9VM_OPT_JITSERVER) */
   };

struct ClassByNameRecord : public ClassValidationRecordWithChain
   {
   ClassByNameRecord(TR_OpaqueClassBlock *clazz,
                     TR_OpaqueClassBlock *beholder)
      : ClassValidationRecordWithChain(TR_ValidateClassByName, clazz),
        _beholder(beholder)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _beholder;
   };

struct ProfiledClassRecord : public ClassValidationRecord
   {
   ProfiledClassRecord(TR_OpaqueClassBlock *clazz, uintptr_t classChainOffset,
                       const AOTCacheClassChainRecord *aotCacheClassChainRecord = NULL)
      : ClassValidationRecord(TR_ValidateProfiledClass),
        _class(clazz), _classChainOffset(classChainOffset)
      {
#if defined(J9VM_OPT_JITSERVER)
      _aotCacheClassChainRecord = aotCacheClassChainRecord;
#endif /* defined(J9VM_OPT_JITSERVER) */
      }

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheClassChainRecord *getAOTCacheClassChainRecord() const { return _aotCacheClassChainRecord; }
#else /* defined(J9VM_OPT_JITSERVER) */
   const AOTCacheClassChainRecord *getAOTCacheClassChainRecord() const { return NULL; }
#endif /* defined(J9VM_OPT_JITSERVER) */

   TR_OpaqueClassBlock *_class;
   uintptr_t _classChainOffset;
#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheClassChainRecord *_aotCacheClassChainRecord;
#endif /* defined(J9VM_OPT_JITSERVER) */
   };

struct ClassFromCPRecord : public ClassValidationRecord
   {
   ClassFromCPRecord(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder, uint32_t cpIndex)
      : ClassValidationRecord(TR_ValidateClassFromCP),
        _class(clazz),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _class;
   TR_OpaqueClassBlock * _beholder;
   uint32_t  _cpIndex;
   };

struct DefiningClassFromCPRecord : public ClassValidationRecord
   {
   DefiningClassFromCPRecord(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder, uint32_t cpIndex, bool isStatic)
      : ClassValidationRecord(TR_ValidateDefiningClassFromCP),
        _class(clazz),
        _beholder(beholder),
        _cpIndex(cpIndex),
        _isStatic(isStatic)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _class;
   TR_OpaqueClassBlock * _beholder;
   uint32_t  _cpIndex;
   bool      _isStatic;
   };

struct StaticClassFromCPRecord : public ClassValidationRecord
   {
   StaticClassFromCPRecord(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder, uint32_t cpIndex)
      : ClassValidationRecord(TR_ValidateStaticClassFromCP),
        _class(clazz),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _class;
   TR_OpaqueClassBlock * _beholder;
   uint32_t  _cpIndex;
   };

struct ArrayClassFromComponentClassRecord : public ClassValidationRecord
   {
   ArrayClassFromComponentClassRecord(TR_OpaqueClassBlock *arrayClass, TR_OpaqueClassBlock *componentClass)
      : ClassValidationRecord(TR_ValidateArrayClassFromComponentClass),
        _arrayClass(arrayClass),
        _componentClass(componentClass)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _arrayClass;
   TR_OpaqueClassBlock * _componentClass;
   };

struct SuperClassFromClassRecord : public ClassValidationRecord
   {
   SuperClassFromClassRecord(TR_OpaqueClassBlock *superClass, TR_OpaqueClassBlock *childClass)
      : ClassValidationRecord(TR_ValidateSuperClassFromClass),
        _superClass(superClass),
        _childClass(childClass)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_superClass;
   TR_OpaqueClassBlock *_childClass;
   };

struct ClassInstanceOfClassRecord : public SymbolValidationRecord
   {
   ClassInstanceOfClassRecord(TR_OpaqueClassBlock *classOne, TR_OpaqueClassBlock *classTwo, bool objectTypeIsFixed, bool castTypeIsFixed, bool isInstanceOf)
      : SymbolValidationRecord(TR_ValidateClassInstanceOfClass),
        _classOne(classOne),
        _classTwo(classTwo),
        _objectTypeIsFixed(objectTypeIsFixed),
        _castTypeIsFixed(castTypeIsFixed),
        _isInstanceOf(isInstanceOf)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_classOne;
   TR_OpaqueClassBlock *_classTwo;
   bool _objectTypeIsFixed;
   bool _castTypeIsFixed;
   bool _isInstanceOf;
   };

struct SystemClassByNameRecord : public ClassValidationRecordWithChain
   {
   SystemClassByNameRecord(TR_OpaqueClassBlock *systemClass)
      : ClassValidationRecordWithChain(TR_ValidateSystemClassByName, systemClass)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();
   };

struct ClassFromITableIndexCPRecord : public ClassValidationRecord
   {
   ClassFromITableIndexCPRecord(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder, uint32_t cpIndex)
      : ClassValidationRecord(TR_ValidateClassFromITableIndexCP),
        _class(clazz),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _class;
   TR_OpaqueClassBlock * _beholder;
   int32_t _cpIndex;

   };

struct DeclaringClassFromFieldOrStaticRecord : public ClassValidationRecord
   {
   DeclaringClassFromFieldOrStaticRecord(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder, uint32_t cpIndex)
      : ClassValidationRecord(TR_ValidateDeclaringClassFromFieldOrStatic),
        _class(clazz),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock * _class;
   TR_OpaqueClassBlock * _beholder;
   uint32_t  _cpIndex;
   };

struct ConcreteSubClassFromClassRecord : public ClassValidationRecord
   {
   ConcreteSubClassFromClassRecord(TR_OpaqueClassBlock *childClass, TR_OpaqueClassBlock *superClass)
      : ClassValidationRecord(TR_ValidateConcreteSubClassFromClass),
        _childClass(childClass),
        _superClass(superClass)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_childClass;
   TR_OpaqueClassBlock *_superClass;
   };

struct ClassChainRecord : public SymbolValidationRecord
   {
   ClassChainRecord(TR_OpaqueClassBlock *clazz, uintptr_t classChainOffset,
                    const AOTCacheClassChainRecord *aotCacheClassChainRecord = NULL)
      : SymbolValidationRecord(TR_ValidateClassChain),
        _class(clazz),
        _classChainOffset(classChainOffset)
      {
#if defined(J9VM_OPT_JITSERVER)
      _aotCacheClassChainRecord = aotCacheClassChainRecord;
#endif /* defined(J9VM_OPT_JITSERVER) */
      }

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheClassChainRecord *getAOTCacheClassChainRecord() const { return _aotCacheClassChainRecord; }
#else /* defined(J9VM_OPT_JITSERVER) */
   const AOTCacheClassChainRecord *getAOTCacheClassChainRecord() const { return NULL; }
#endif /* defined(J9VM_OPT_JITSERVER) */

   TR_OpaqueClassBlock *_class;
   uintptr_t _classChainOffset;
#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheClassChainRecord *_aotCacheClassChainRecord;
#endif /* defined(J9VM_OPT_JITSERVER) */
   };

struct MethodValidationRecord : public SymbolValidationRecord
   {
   MethodValidationRecord(TR_ExternalRelocationTargetKind kind, TR_OpaqueMethodBlock *method)
      : SymbolValidationRecord(kind),
        _method(method),
        _definingClass(NULL)
      {}

   TR_OpaqueClassBlock *definingClass()
      {
      TR_ASSERT(_definingClass, "defining class must be already cached");
      return _definingClass;
      }

   TR_OpaqueClassBlock *definingClass(TR_J9VM *fe)
      {
      _definingClass = fe->getClassOfMethod(_method);
      return _definingClass;
      }

   TR_OpaqueMethodBlock *_method;
   TR_OpaqueClassBlock *_definingClass;
   };

struct MethodFromClassRecord : public MethodValidationRecord
   {
   MethodFromClassRecord(TR_OpaqueMethodBlock *method, TR_OpaqueClassBlock *beholder, uint32_t index)
      : MethodValidationRecord(TR_ValidateMethodFromClass, method),
        _beholder(beholder),
        _index(index)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   uint32_t _index;
   };

struct StaticMethodFromCPRecord : public MethodValidationRecord
   {
   StaticMethodFromCPRecord(TR_OpaqueMethodBlock *method,
                               TR_OpaqueClassBlock *beholder,
                               int32_t cpIndex)
      : MethodValidationRecord(TR_ValidateStaticMethodFromCP, method),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   int32_t _cpIndex;
   };

struct SpecialMethodFromCPRecord : public MethodValidationRecord
   {
   SpecialMethodFromCPRecord(TR_OpaqueMethodBlock *method,
                             TR_OpaqueClassBlock *beholder,
                             int32_t cpIndex)
      : MethodValidationRecord(TR_ValidateSpecialMethodFromCP, method),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   int32_t _cpIndex;
   };

struct VirtualMethodFromCPRecord : public MethodValidationRecord
   {
   VirtualMethodFromCPRecord(TR_OpaqueMethodBlock *method,
                             TR_OpaqueClassBlock *beholder,
                             int32_t cpIndex)
      : MethodValidationRecord(TR_ValidateVirtualMethodFromCP, method),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   int32_t _cpIndex;
   };

struct VirtualMethodFromOffsetRecord : public MethodValidationRecord
   {
   VirtualMethodFromOffsetRecord(TR_OpaqueMethodBlock *method,
                                 TR_OpaqueClassBlock *beholder,
                                 int32_t virtualCallOffset,
                                 bool ignoreRtResolve)
      : MethodValidationRecord(TR_ValidateVirtualMethodFromOffset, method),
        _beholder(beholder),
        _virtualCallOffset(virtualCallOffset),
        _ignoreRtResolve(ignoreRtResolve)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   int32_t _virtualCallOffset;
   bool _ignoreRtResolve;
   };

struct InterfaceMethodFromCPRecord : public MethodValidationRecord
   {
   InterfaceMethodFromCPRecord(TR_OpaqueMethodBlock *method,
                               TR_OpaqueClassBlock *beholder,
                               TR_OpaqueClassBlock *lookup,
                               int32_t cpIndex)
      : MethodValidationRecord(TR_ValidateInterfaceMethodFromCP, method),
        _beholder(beholder),
        _lookup(lookup),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   TR_OpaqueClassBlock *_lookup;
   int32_t _cpIndex;
   };

struct MethodFromClassAndSigRecord : public MethodValidationRecord
   {
   MethodFromClassAndSigRecord(TR_OpaqueMethodBlock *method,
                               TR_OpaqueClassBlock *lookupClass,
                               TR_OpaqueClassBlock *beholder)
      : MethodValidationRecord(TR_ValidateMethodFromClassAndSig, method),
        _lookupClass(lookupClass),
        _beholder(beholder)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_lookupClass;
   TR_OpaqueClassBlock *_beholder;
   };

struct StackWalkerMaySkipFramesRecord : public SymbolValidationRecord
   {
   StackWalkerMaySkipFramesRecord(TR_OpaqueMethodBlock *method,
                                  TR_OpaqueClassBlock *methodClass,
                                  bool skipFrames)
      : SymbolValidationRecord(TR_ValidateStackWalkerMaySkipFramesRecord),
        _method(method),
        _methodClass(methodClass),
        _skipFrames(skipFrames)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueMethodBlock *_method;
   TR_OpaqueClassBlock *_methodClass;
   bool _skipFrames;
   };

struct ClassInfoIsInitialized : public SymbolValidationRecord
   {
   ClassInfoIsInitialized(TR_OpaqueClassBlock *clazz, bool isInitialized)
      : SymbolValidationRecord(TR_ValidateClassInfoIsInitialized),
        _class(clazz),
        _isInitialized(isInitialized)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_class;
   bool _isInitialized;
   };

struct MethodFromSingleImplementer : public MethodValidationRecord
   {
   MethodFromSingleImplementer(TR_OpaqueMethodBlock *method,
                               TR_OpaqueClassBlock *thisClass,
                               int32_t cpIndexOrVftSlot,
                               TR_OpaqueMethodBlock *callerMethod,
                               TR_YesNoMaybe useGetResolvedInterfaceMethod)
      : MethodValidationRecord(TR_ValidateMethodFromSingleImplementer, method),
        _thisClass(thisClass),
        _cpIndexOrVftSlot(cpIndexOrVftSlot),
        _callerMethod(callerMethod),
        _useGetResolvedInterfaceMethod(useGetResolvedInterfaceMethod)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_thisClass;
   int32_t _cpIndexOrVftSlot;
   TR_OpaqueMethodBlock *_callerMethod;
   TR_YesNoMaybe _useGetResolvedInterfaceMethod;
   };

struct MethodFromSingleInterfaceImplementer : public MethodValidationRecord
   {
   MethodFromSingleInterfaceImplementer(TR_OpaqueMethodBlock *method,
                                        TR_OpaqueClassBlock *thisClass,
                                        int32_t cpIndex,
                                        TR_OpaqueMethodBlock *callerMethod)
      : MethodValidationRecord(TR_ValidateMethodFromSingleInterfaceImplementer, method),
        _thisClass(thisClass),
        _cpIndex(cpIndex),
        _callerMethod(callerMethod)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_thisClass;
   int32_t _cpIndex;
   TR_OpaqueMethodBlock *_callerMethod;
   };

struct MethodFromSingleAbstractImplementer : public MethodValidationRecord
   {
   MethodFromSingleAbstractImplementer(TR_OpaqueMethodBlock *method,
                                       TR_OpaqueClassBlock *thisClass,
                                       int32_t vftSlot,
                                       TR_OpaqueMethodBlock *callerMethod)
      : MethodValidationRecord(TR_ValidateMethodFromSingleAbstractImplementer, method),
        _thisClass(thisClass),
        _vftSlot(vftSlot),
        _callerMethod(callerMethod)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_thisClass;
   int32_t _vftSlot;
   TR_OpaqueMethodBlock *_callerMethod;
   };

struct ImproperInterfaceMethodFromCPRecord : public MethodValidationRecord
   {
   ImproperInterfaceMethodFromCPRecord(TR_OpaqueMethodBlock *method,
                               TR_OpaqueClassBlock *beholder,
                               int32_t cpIndex)
      : MethodValidationRecord(TR_ValidateImproperInterfaceMethodFromCP, method),
        _beholder(beholder),
        _cpIndex(cpIndex)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_beholder;
   int32_t _cpIndex;
   };

struct J2IThunkFromMethodRecord : public SymbolValidationRecord
   {
   J2IThunkFromMethodRecord(void *thunk, TR_OpaqueMethodBlock *method)
      : SymbolValidationRecord(TR_ValidateJ2IThunkFromMethod),
        _thunk(thunk),
        _method(method)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   void *_thunk;
   TR_OpaqueMethodBlock *_method;
   };

struct IsClassVisibleRecord : public SymbolValidationRecord
   {
   IsClassVisibleRecord(TR_OpaqueClassBlock *sourceClass, TR_OpaqueClassBlock *destClass, bool isVisible)
      : SymbolValidationRecord(TR_ValidateIsClassVisible),
        _sourceClass(sourceClass),
        _destClass(destClass),
        _isVisible(isVisible)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueClassBlock *_sourceClass;
   TR_OpaqueClassBlock *_destClass;
   bool _isVisible;
   };

struct DynamicMethodFromCallsiteIndexRecord : public MethodValidationRecord
   {
   DynamicMethodFromCallsiteIndexRecord(TR_OpaqueMethodBlock *method,
                                        TR_OpaqueMethodBlock *caller,
                                        int32_t callsiteIndex,
                                        bool appendixObjectNull)
      : MethodValidationRecord(TR_ValidateDynamicMethodFromCallsiteIndex, method),
      _caller(caller),
      _callsiteIndex(callsiteIndex),
      _appendixObjectNull(appendixObjectNull)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueMethodBlock *_caller;
   int32_t _callsiteIndex;
   bool _appendixObjectNull;
   };

struct HandleMethodFromCPIndex  : public MethodValidationRecord
   {
   HandleMethodFromCPIndex(TR_OpaqueMethodBlock *method,
                           TR_OpaqueMethodBlock *caller,
                           int32_t cpIndex,
                           bool appendixObjectNull)
      : MethodValidationRecord(TR_ValidateHandleMethodFromCPIndex, method),
      _caller(caller),
      _cpIndex(cpIndex),
      _appendixObjectNull(appendixObjectNull)
      {}

   virtual bool isLessThanWithinKind(SymbolValidationRecord *other);
   virtual void printFields();

   TR_OpaqueMethodBlock *_caller;
   int32_t _cpIndex;
   bool _appendixObjectNull;
   };

class SymbolValidationManager
   {
public:
   TR_ALLOC(TR_MemoryBase::SymbolValidationManager)

   SymbolValidationManager(TR::Region &region, TR_ResolvedMethod *compilee, TR::Compilation *comp);

   struct SystemClassNotWorthRemembering
      {
      const char *_className;
      TR_OpaqueClassBlock *_clazz;
      bool _checkIsSuperClass;
      };

   #define WELL_KNOWN_CLASS_COUNT 9

   void populateWellKnownClasses();
   bool validateWellKnownClasses(const uintptr_t *wellKnownClassChainOffsets);
   bool isWellKnownClass(TR_OpaqueClassBlock *clazz);
   bool classCanSeeWellKnownClasses(TR_OpaqueClassBlock *clazz);
   const void *wellKnownClassChainOffsets() const { return _wellKnownClassChainOffsets; }
#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheWellKnownClassesRecord *aotCacheWellKnownClassesRecord() const { return _aotCacheWellKnownClassesRecord; }
#endif /* defined(J9VM_OPT_JITSERVER */

   enum Presence
      {
      SymRequired,
      SymOptional
      };

   void* getValueFromSymbolID(uint16_t id, TR::SymbolType type, Presence presence = SymRequired);
   TR_OpaqueClassBlock *getClassFromID(uint16_t id, Presence presence = SymRequired);
   J9Class *getJ9ClassFromID(uint16_t id, Presence presence = SymRequired);
   TR_OpaqueMethodBlock *getMethodFromID(uint16_t id, Presence presence = SymRequired);
   J9Method *getJ9MethodFromID(uint16_t id, Presence presence = SymRequired);

   uint16_t tryGetSymbolIDFromValue(void *value);
   uint16_t getSymbolIDFromValue(void *value);

   bool isAlreadyValidated(void *value)
      {
      return inHeuristicRegion() || tryGetSymbolIDFromValue(value) != NO_ID;
      }

   bool addClassByNameRecord(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder);
   bool addProfiledClassRecord(TR_OpaqueClassBlock *clazz);
   bool addClassFromCPRecord(TR_OpaqueClassBlock *clazz, J9ConstantPool *constantPoolOfBeholder, uint32_t cpIndex);
   bool addDefiningClassFromCPRecord(TR_OpaqueClassBlock *clazz, J9ConstantPool *constantPoolOfBeholder, uint32_t cpIndex, bool isStatic = false);
   bool addStaticClassFromCPRecord(TR_OpaqueClassBlock *clazz, J9ConstantPool *constantPoolOfBeholder, uint32_t cpIndex);
   bool addArrayClassFromComponentClassRecord(TR_OpaqueClassBlock *arrayClass, TR_OpaqueClassBlock *componentClass);
   bool addSuperClassFromClassRecord(TR_OpaqueClassBlock *superClass, TR_OpaqueClassBlock *childClass);
   bool addClassInstanceOfClassRecord(TR_OpaqueClassBlock *classOne, TR_OpaqueClassBlock *classTwo, bool objectTypeIsFixed, bool castTypeIsFixed, bool isInstanceOf);
   bool addSystemClassByNameRecord(TR_OpaqueClassBlock *systemClass);
   bool addClassFromITableIndexCPRecord(TR_OpaqueClassBlock *clazz, J9ConstantPool *constantPoolOfBeholder, int32_t cpIndex);
   bool addDeclaringClassFromFieldOrStaticRecord(TR_OpaqueClassBlock *clazz, J9ConstantPool *constantPoolOfBeholder, int32_t cpIndex);
   bool addConcreteSubClassFromClassRecord(TR_OpaqueClassBlock *childClass, TR_OpaqueClassBlock *superClass);

   bool addMethodFromClassRecord(TR_OpaqueMethodBlock *method, TR_OpaqueClassBlock *beholder, uint32_t index);
   bool addStaticMethodFromCPRecord(TR_OpaqueMethodBlock *method, J9ConstantPool *cp, int32_t cpIndex);
   bool addSpecialMethodFromCPRecord(TR_OpaqueMethodBlock *method, J9ConstantPool *cp, int32_t cpIndex);
   bool addVirtualMethodFromCPRecord(TR_OpaqueMethodBlock *method, J9ConstantPool *cp, int32_t cpIndex);
   bool addVirtualMethodFromOffsetRecord(TR_OpaqueMethodBlock *method, TR_OpaqueClassBlock *beholder, int32_t virtualCallOffset, bool ignoreRtResolve);
   bool addInterfaceMethodFromCPRecord(TR_OpaqueMethodBlock *method, TR_OpaqueClassBlock *beholder, TR_OpaqueClassBlock *lookup, int32_t cpIndex);
   bool addImproperInterfaceMethodFromCPRecord(TR_OpaqueMethodBlock *method, J9ConstantPool *cp, int32_t cpIndex);
   bool addMethodFromClassAndSignatureRecord(TR_OpaqueMethodBlock *method, TR_OpaqueClassBlock *methodClass, TR_OpaqueClassBlock *beholder);
   bool addMethodFromSingleImplementerRecord(TR_OpaqueMethodBlock *method,
                                             TR_OpaqueClassBlock *thisClass,
                                             int32_t cpIndexOrVftSlot,
                                             TR_OpaqueMethodBlock *callerMethod,
                                             TR_YesNoMaybe useGetResolvedInterfaceMethod);
   bool addMethodFromSingleInterfaceImplementerRecord(TR_OpaqueMethodBlock *method,
                                           TR_OpaqueClassBlock *thisClass,
                                           int32_t cpIndex,
                                           TR_OpaqueMethodBlock *callerMethod);
   bool addMethodFromSingleAbstractImplementerRecord(TR_OpaqueMethodBlock *method,
                                          TR_OpaqueClassBlock *thisClass,
                                          int32_t vftSlot,
                                          TR_OpaqueMethodBlock *callerMethod);
   bool addDynamicMethodFromCallsiteIndex(TR_OpaqueMethodBlock *method, TR_OpaqueMethodBlock *caller, int32_t callsiteIndex, bool appendixObjectNull);
   bool addHandleMethodFromCPIndex(TR_OpaqueMethodBlock *method, TR_OpaqueMethodBlock *caller, int32_t cpIndex, bool appendixObjectNull);

   bool addStackWalkerMaySkipFramesRecord(TR_OpaqueMethodBlock *method, TR_OpaqueClassBlock *methodClass, bool skipFrames);
   bool addClassInfoIsInitializedRecord(TR_OpaqueClassBlock *clazz, bool isInitialized);
   void addJ2IThunkFromMethodRecord(void *thunk, TR_OpaqueMethodBlock *method);
   bool addIsClassVisibleRecord(TR_OpaqueClassBlock *sourceClass, TR_OpaqueClassBlock *destClass, bool isVisible);



   bool validateClassByNameRecord(uint16_t classID, uint16_t beholderID, uintptr_t *classChain);
   bool validateProfiledClassRecord(uint16_t classID, void *classChainIdentifyingLoader, void *classChainForClassBeingValidated);
   bool validateClassFromCPRecord(uint16_t classID, uint16_t beholderID, uint32_t cpIndex);
   bool validateDefiningClassFromCPRecord(uint16_t classID, uint16_t beholderID, uint32_t cpIndex, bool isStatic);
   bool validateStaticClassFromCPRecord(uint16_t classID, uint16_t beholderID, uint32_t cpIndex);
   bool validateArrayClassFromComponentClassRecord(uint16_t arrayClassID, uint16_t componentClassID);
   bool validateSuperClassFromClassRecord(uint16_t superClassID, uint16_t childClassID);
   bool validateClassInstanceOfClassRecord(uint16_t classOneID, uint16_t classTwoID, bool objectTypeIsFixed, bool castTypeIsFixed, bool wasInstanceOf);
   bool validateSystemClassByNameRecord(uint16_t systemClassID, uintptr_t *classChain);
   bool validateClassFromITableIndexCPRecord(uint16_t classID, uint16_t beholderID, uint32_t cpIndex);
   bool validateDeclaringClassFromFieldOrStaticRecord(uint16_t definingClassID, uint16_t beholderID, int32_t cpIndex);
   bool validateConcreteSubClassFromClassRecord(uint16_t childClassID, uint16_t superClassID);

   bool validateClassChainRecord(uint16_t classID, void *classChain);

   bool validateMethodFromClassRecord(uint16_t methodID, uint16_t beholderID, uint32_t index);
   bool validateStaticMethodFromCPRecord(uint16_t methodID, uint16_t definingClassID, uint16_t beholderID, int32_t cpIndex);
   bool validateSpecialMethodFromCPRecord(uint16_t methodID, uint16_t definingClassID, uint16_t beholderID, int32_t cpIndex);
   bool validateVirtualMethodFromCPRecord(uint16_t methodID, uint16_t definingClassID, uint16_t beholderID, int32_t cpIndex);
   bool validateVirtualMethodFromOffsetRecord(uint16_t methodID, uint16_t definingClassID, uint16_t beholderID, int32_t virtualCallOffset, bool ignoreRtResolve);
   bool validateInterfaceMethodFromCPRecord(uint16_t methodID, uint16_t definingClassID, uint16_t beholderID, uint16_t lookupID, int32_t cpIndex);
   bool validateImproperInterfaceMethodFromCPRecord(uint16_t methodID, uint16_t definingClassID, uint16_t beholderID, int32_t cpIndex);
   bool validateMethodFromClassAndSignatureRecord(uint16_t methodID, uint16_t definingClassID, uint16_t lookupClassID, uint16_t beholderID, J9ROMMethod *romMethod);
   bool validateMethodFromSingleImplementerRecord(uint16_t methodID,
                                                  uint16_t definingClassID,
                                                  uint16_t thisClassID,
                                                  int32_t cpIndexOrVftSlot,
                                                  uint16_t callerMethodID,
                                                  TR_YesNoMaybe useGetResolvedInterfaceMethod);
   bool validateMethodFromSingleInterfaceImplementerRecord(uint16_t methodID,
                                                uint16_t definingClassID,
                                                uint16_t thisClassID,
                                                int32_t cpIndex,
                                                uint16_t callerMethodID);
   bool validateMethodFromSingleAbstractImplementerRecord(uint16_t methodID,
                                               uint16_t definingClassID,
                                               uint16_t thisClassID,
                                               int32_t vftSlot,
                                               uint16_t callerMethodID);
   bool validateDynamicMethodFromCallsiteIndex(uint16_t methodID,
                                               uint16_t callerID,
                                               int32_t callsiteIndex,
                                               bool appendixObjectNull,
                                               uint16_t definingClassID,
                                               uint32_t methodIndex);
   bool validateHandleMethodFromCPIndex(uint16_t methodID,
                                        uint16_t callerID,
                                        int32_t cpIndex,
                                        bool appendixObjectNull,
                                        uint16_t definingClassID,
                                        uint32_t methodIndex);

   bool validateStackWalkerMaySkipFramesRecord(uint16_t methodID, uint16_t methodClassID, bool couldSkipFrames);
   bool validateClassInfoIsInitializedRecord(uint16_t classID, bool wasInitialized);

   // For J2IThunkFromMethod records, the actual thunk is loaded if necessary
   // in TR_RelocationRecordValidateJ2IThunkFromMethod::applyRelocation() so
   // that the thunk loading logic can be confined to RelocationRecord.cpp.
   bool validateJ2IThunkFromMethodRecord(uint16_t thunkID, void *thunk);

   bool validateIsClassVisibleRecord(uint16_t sourceClassID, uint16_t destClassID, bool wasVisible);


   TR_OpaqueClassBlock *getBaseComponentClass(TR_OpaqueClassBlock *clazz, int32_t & numDims);

   typedef TR::list<SymbolValidationRecord *, TR::Region&> SymbolValidationRecordList;

   SymbolValidationRecordList& getValidationRecordList() { return _symbolValidationRecords; }

   void enterHeuristicRegion() { _heuristicRegion++; }
   void exitHeuristicRegion() { _heuristicRegion--; }
   bool inHeuristicRegion() { return (_heuristicRegion > 0); }

   static bool assertionsAreFatal();

   static int getSystemClassesNotWorthRememberingCount();

#if defined(J9VM_OPT_JITSERVER)
   static void populateSystemClassesNotWorthRemembering(ClientSessionData *clientData);
#endif /* defined(J9VM_OPT_JITSERVER) */

   SystemClassNotWorthRemembering *getSystemClassNotWorthRemembering(int idx);

   static const int SYSTEM_CLASSES_NOT_WORTH_REMEMBERING_COUNT = 2;

private:

   static const uint16_t NO_ID = 0;
   static const uint16_t FIRST_ID = 1;

   uint16_t getNewSymbolID();

   bool shouldNotDefineSymbol(void *value) { return value == NULL || inHeuristicRegion(); }
   bool abandonRecord(TR::SymbolValidationRecord *record);

   bool recordExists(TR::SymbolValidationRecord *record);
   bool anyClassFromCPRecordExists(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder);
   void appendNewRecord(void *value, TR::SymbolValidationRecord *record);
   void appendRecordIfNew(void *value, TR::SymbolValidationRecord *record);

   struct ClassChainInfo
      {
      ClassChainInfo()
         : _baseComponent(NULL), _baseComponentClassChainOffset(TR_SharedCache::INVALID_CLASS_CHAIN_OFFSET), _arrayDims(0)
         {
#if defined(J9VM_OPT_JITSERVER)
         _baseComponentAOTCacheClassChainRecord = NULL;
#endif /* defined(J9VM_OPT_JITSERVER) */
         }

      TR_OpaqueClassBlock *_baseComponent;
      uintptr_t _baseComponentClassChainOffset;
      int32_t _arrayDims;
#if defined(J9VM_OPT_JITSERVER)
      const AOTCacheClassChainRecord *_baseComponentAOTCacheClassChainRecord;
#endif /* defined(J9VM_OPT_JITSERVER) */
      };

   bool getClassChainInfo(TR_OpaqueClassBlock *clazz, TR::SymbolValidationRecord *record, ClassChainInfo &info);
   void appendClassChainInfoRecords(TR_OpaqueClassBlock *clazz, const ClassChainInfo &info);

   bool addVanillaRecord(void *value, TR::SymbolValidationRecord *record);
   bool addClassRecord(TR_OpaqueClassBlock *clazz, TR::ClassValidationRecord *record);
   bool addClassRecordWithChain(TR::ClassValidationRecordWithChain *record);
   void addMultipleArrayRecords(TR_OpaqueClassBlock *clazz, int arrayDims);
   bool addMethodRecord(TR::MethodValidationRecord *record);
   bool skipFieldRefClassRecord(TR_OpaqueClassBlock *definingClass, TR_OpaqueClassBlock *beholder, uint32_t cpIndex);

   bool validateSymbol(uint16_t idToBeValidated, void *validValue, TR::SymbolType type);
   bool validateSymbol(uint16_t idToBeValidated, TR_OpaqueClassBlock *clazz);
   bool validateSymbol(uint16_t idToBeValidated, J9Class *clazz);
   bool validateSymbol(uint16_t methodID, uint16_t definingClassID, TR_OpaqueMethodBlock *method);
   bool validateSymbol(uint16_t methodID, uint16_t definingClassID, J9Method *method);

   bool isDefinedID(uint16_t id);
   void setValueOfSymbolID(uint16_t id, void *value, TR::SymbolType type);
   void defineGuaranteedID(void *value, TR::SymbolType type);

   /**
    * @brief Heuristic to determine whether a class is worth remembering (and hence
    *        worth considering during optimization) in an AOT compilation.
    *
    * @param clazz : The class being considered
    * @return true if worth remembering, false otherwise.
    */
   bool isClassWorthRemembering(TR_OpaqueClassBlock *clazz);

   /* Monotonically increasing IDs */
   uint16_t _symbolID;

   uint32_t _heuristicRegion;

   TR::Region &_region;

   TR::Compilation * const _comp;
   J9VMThread * const _vmThread;
   TR_J9VM * const _fej9; // DEFAULT_VM
   TR_Memory * const _trMemory;
   TR_PersistentCHTable * const _chTable;

   TR_OpaqueClassBlock *_rootClass;
   const void *_wellKnownClassChainOffsets;
#if defined(J9VM_OPT_JITSERVER)
   const AOTCacheWellKnownClassesRecord *_aotCacheWellKnownClassesRecord;
#endif /* defined(J9VM_OPT_JITSERVER */

   /* List of validation records to be written to the AOT buffer */
   SymbolValidationRecordList _symbolValidationRecords;

   typedef TR::typed_allocator<SymbolValidationRecord*, TR::Region&> RecordPtrAlloc;
   typedef std::set<SymbolValidationRecord*, LessSymbolValidationRecord, RecordPtrAlloc> RecordSet;
   RecordSet _alreadyGeneratedRecords;

   typedef TR::typed_allocator<std::pair<void* const, uint16_t>, TR::Region&> ValueToSymbolAllocator;
   typedef std::less<void*> ValueToSymbolComparator;
   typedef std::map<void*, uint16_t, ValueToSymbolComparator, ValueToSymbolAllocator> ValueToSymbolMap;

   struct TypedValue
      {
      void *_value;
      TR::SymbolType _type;
      bool _hasValue;
      };

   typedef TR::typed_allocator<TypedValue, TR::Region&> SymbolToValueAllocator;
   typedef std::vector<TypedValue, SymbolToValueAllocator> SymbolToValueTable;

   typedef TR::typed_allocator<void*, TR::Region&> SeenValuesAlloc;
   typedef std::less<void*> SeenValuesComparator;
   typedef std::set<void*, SeenValuesComparator, SeenValuesAlloc> SeenValuesSet;

   /* Used for AOT Compile */
   ValueToSymbolMap _valueToSymbolMap;

   /* Used for AOT Load */
   SymbolToValueTable _symbolToValueTable;

   SeenValuesSet _seenValuesSet;

   typedef TR::typed_allocator<TR_OpaqueClassBlock*, TR::Region&> ClassAllocator;
   typedef std::vector<TR_OpaqueClassBlock*, ClassAllocator> ClassVector;
   ClassVector _wellKnownClasses;

   typedef TR::typed_allocator<J9ClassLoader*, TR::Region&> LoaderAllocator;
   typedef std::vector<J9ClassLoader*, LoaderAllocator> LoaderVector;
   LoaderVector _loadersOkForWellKnownClasses;

   // Remember which classes have already been found in which beholders'
   // constant pools, regardless of CP index. If a class C has already been
   // found in the constant pool of class D (producing a ClassFromCP record),
   // then ClassByName(C, D) is redundant.
   struct ClassFromAnyCPIndex
      {
      TR_OpaqueClassBlock *clazz;
      TR_OpaqueClassBlock *beholder;

      ClassFromAnyCPIndex(TR_OpaqueClassBlock *clazz, TR_OpaqueClassBlock *beholder)
         : clazz(clazz), beholder(beholder) { }
      };

   struct LessClassFromAnyCPIndex
      {
      bool operator()(const ClassFromAnyCPIndex &a, const ClassFromAnyCPIndex &b) const
         {
         std::less<TR_OpaqueClassBlock*> lt;
         if (lt(a.clazz, b.clazz))
            return true;
         else if (lt(b.clazz, a.clazz))
            return false;
         else
            return lt(a.beholder, b.beholder);
         }
      };

   typedef TR::typed_allocator<ClassFromAnyCPIndex, TR::Region&> ClassFromAnyCPIndexAlloc;
   typedef std::set<ClassFromAnyCPIndex, LessClassFromAnyCPIndex, ClassFromAnyCPIndexAlloc> ClassFromAnyCPIndexSet;
   ClassFromAnyCPIndexSet _classesFromAnyCPIndex;

   static SystemClassNotWorthRemembering _systemClassesNotWorthRemembering[];
   };

}

#endif //SYMBOL_VALIDATION_MANAGER_INCL
