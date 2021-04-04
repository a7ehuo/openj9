/*******************************************************************************
 * Copyright (c) 2021, 2021 IBM Corp. and others
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
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#include "optimizer/TreeLowering.hpp"

#include "compile/Compilation.hpp"
#include "compile/SymbolReferenceTable.hpp"
#include "il/Block.hpp"
#include "il/Block_inlines.hpp"
#include "infra/ILWalk.hpp"
#include "optimizer/J9TransformUtil.hpp"

const char *
TR::TreeLowering::optDetailString() const throw()
   {
   return "O^O TREE LOWERING: ";
   }

int32_t
TR::TreeLowering::perform()
   {
   if (!TR::Compiler->om.areValueTypesEnabled())
      {
      return 0;
      }

   TR::ResolvedMethodSymbol* methodSymbol = comp()->getMethodSymbol();
   for (TR::PreorderNodeIterator nodeIter(methodSymbol->getFirstTreeTop(), comp()); nodeIter != NULL; ++nodeIter)
      {
      TR::Node* node = nodeIter.currentNode();
      TR::TreeTop* tt = nodeIter.currentTree();

      lowerValueTypeOperations(nodeIter, node, tt);
      }

   return 0;
   }

void
TR::TreeLowering::moveNodeToEndOfBlock(TR::Block* const block, TR::TreeTop* const tt, TR::Node* const node, bool isAddress)
   {
   TR::Compilation* comp = self()->comp();
   TR::TreeTop* blockExit = block->getExit();
   TR::TreeTop* iterTT = tt->getNextTreeTop();

   if (iterTT != blockExit)
      {
      if (trace())
         {
         traceMsg(comp, "Moving treetop containing node n%dn [%p] for helper call to end of prevBlock in preparation of final block split\n", tt->getNode()->getGlobalIndex(), tt->getNode());
         }

      // Remove TreeTop for call node, and gather it and the treetops for stores that
      // resulted from un-commoning in a TreeTop chain from tt to lastTTForCallBlock
      tt->unlink(false);
      TR::TreeTop* lastTTForCallBlock = tt;

      while (iterTT != blockExit)
         {
         TR::TreeTop* nextTT = iterTT->getNextTreeTop();
         TR::ILOpCodes op = iterTT->getNode()->getOpCodeValue();
         bool opCodeCondition = false;

         if (isAddress)
            {
            opCodeCondition = (op == TR::aRegStore || op == TR::astore);
            }
         else
            {
            opCodeCondition = (op == TR::iRegStore || op == TR::istore);
            }

         if (opCodeCondition && iterTT->getNode()->getFirstChild() == node)
            {
            if (trace())
               {
               traceMsg(comp, "Moving treetop containing node n%dn [%p] for store of helper result to end of prevBlock in preparation of final block split\n", iterTT->getNode()->getGlobalIndex(), iterTT->getNode());
               }

            // Remove store node from prevBlock temporarily
            iterTT->unlink(false);
            lastTTForCallBlock->join(iterTT);
            lastTTForCallBlock = iterTT;
            }

         iterTT = nextTT;
         }

      // Move the treetops that were gathered for the call and any stores of the
      // result to the end of the block in preparation for the split of the call block
      blockExit->getPrevTreeTop()->join(tt);
      lastTTForCallBlock->join(blockExit);
      }
   }

/**
 * @brief Perform lowering related to Valhalla value types
 *
 */
void
TR::TreeLowering::lowerValueTypeOperations(TR::PreorderNodeIterator& nodeIter, TR::Node* node, TR::TreeTop* tt)
   {
   TR::SymbolReferenceTable * symRefTab = comp()->getSymRefTab();
   static char *disableInliningCheckAastore = feGetEnv("TR_DisableVT_AASTORE_Inlining");

   if (node->getOpCode().isCall())
      {
      if (symRefTab->isNonHelper(node->getSymbolReference(), TR::SymbolReferenceTable::objectEqualityComparisonSymbol))
         {
         // turn the non-helper call into a VM helper call
         node->setSymbolReference(symRefTab->findOrCreateAcmpHelperSymbolRef());
         static const bool disableAcmpFastPath =  NULL != feGetEnv("TR_DisableAcmpFastpath");
         if (!disableAcmpFastPath)
            {
            fastpathAcmpHelper(node, tt);
            }
         }
      else if (node->getSymbolReference()->getReferenceNumber() == TR_ldFlattenableArrayElement)
         {
         static char *disableInliningCheckAaload = feGetEnv("TR_DisableVT_AALOAD_Inlining");

         if (!disableInliningCheckAaload)
            {
            const char *counterName = TR::DebugCounter::debugCounterName(comp(), "vt-helper/inlinecheck/aaload/(%s)/bc=%d",
                                                            comp()->signature(), node->getByteCodeIndex());
            TR::DebugCounter::incStaticDebugCounter(comp(), counterName);

            lowerLoadArrayElement(nodeIter, node, tt);
            }
         }
      else if (node->getSymbolReference()->getReferenceNumber() == TR_strFlattenableArrayElement)
         {
         if (!disableInliningCheckAastore)
            {
            const char *counterName = TR::DebugCounter::debugCounterName(comp(), "vt-helper/inlinecheck/aastore/(%s)/bc=%d",
                                                            comp()->signature(), node->getByteCodeIndex());
            TR::DebugCounter::incStaticDebugCounter(comp(), counterName);

            lowerStoreArrayElement(nodeIter, node, tt);
            }
         }
      }
   // If inlining check for aastore is enabled, the NULLCHK on the value reference is
   // taken care of by lowerStoreArrayElement.
   else if (node->getOpCodeValue() == TR::ArrayStoreCHK && disableInliningCheckAastore)
      {
      lowerArrayStoreCHK(node, tt);
      }
   }

/**
 * @brief Add checks to skip (fast-path) acmpHelper call
 *
 * @details
 *
 * This transformation adds checks for the cases where the acmp can be performed
 * without calling the VM helper. The transformed Trees represent the following operation:
 *
 * 1. If the address of lhs and rhs are the same, produce an eq (true) result
 *    and skip the call (note the two objects must be the same regardless of
 *    whether they are value types are reference types)
 * 2. Otherwise, do VM helper call
 *
 * The transformation looks as follows:
 *
 *  +----------------------+
 *  |ttprev                |
 *  |treetop               |
 *  |  icall acmpHelper    |
 *  |    aload lhs         |
 *  |    aload rhs         |
 *  |ificmpeq --> ...      |
 *  |  ==> icall           |
 *  |  iconst 0            |
 *  |BBEnd                 |
 *  +----------------------+
 *
 *  ...becomes...
 *
 *  +----------------------+
 *  |ttprev                |
 *  |iRegStore x           |
 *  |  iconst 1            |
 *  |ifacmpeq  -->---------*---------+
 *  |  aload lhs           |         |
 *  |  aload rhs           |         |
 *  |  GlRegDeps           |         |
 *  |    PassThrough x     |         |
 *  |      ==> iconst 1    |         |
 *  |    PassThrough ...   |         |
 *  |BBEnd                 |         |
 *  +----------------------+         |
 *  |BBStart (extension)   |         |
 *  |iRegStore x           |         |
 *  |  icall acmpHelper    |         |
 *  |    aload lhs         |         |
 *  |    aload rhs         |         |
 *  |BBEnd                 |         |
 *  |  GlRegDeps           |         |
 *  |    PassThrough x     |         |
 *  |      ==> icall acmpHelper      |
 *  |    PassThrough ...   |         |
 *  +----------------------+         |
 *        |                          |
 *        +--------------------------+
 *        |
 *        v
 *  +-----------------+
 *  |BBStart
 *  |ificmpeq --> ... |
 *  |  iRegLoad x     |
 *  |  iconst 0       |
 *  |BBEnd            |
 *  +-----------------+
 *
 * Any GlRegDeps on the extension block are created by OMR::Block::splitPostGRA
 * while those on the ifacmpeq at the end of the first block are copies of those,
 * with the exception of any register (x, above) holding the result of the compare
 *
 * @param node is the current node in the tree walk
 * @param tt is the treetop at the root of the tree ancoring the current node
 *
 */
void
TR::TreeLowering::fastpathAcmpHelper(TR::Node *node, TR::TreeTop *tt)
   {
   TR::Compilation* comp = self()->comp();
   TR::CFG* cfg = comp->getFlowGraph();
   cfg->invalidateStructure();

   // anchor call node after split point to ensure the returned value goes into
   // either a temp or a global register
   auto* anchoredCallTT = TR::TreeTop::create(comp, tt, TR::Node::create(TR::treetop, 1, node));
   if (trace())
      traceMsg(comp, "Anchoring call node under treetop n%dn (0x%p)\n", anchoredCallTT->getNode()->getGlobalIndex(), anchoredCallTT->getNode());

   // anchor the call arguments just before the call
   // this ensures the values are live before the call so that we can
   // propagate their values in global registers if needed
   auto* anchoredCallArg1TT = TR::TreeTop::create(comp, tt->getPrevTreeTop(), TR::Node::create(TR::treetop, 1, node->getFirstChild()));
   auto* anchoredCallArg2TT = TR::TreeTop::create(comp, tt->getPrevTreeTop(), TR::Node::create(TR::treetop, 1, node->getSecondChild()));
   if (trace())
      {
      traceMsg(comp, "Anchoring call arguments n%dn and n%dn under treetops n%dn and n%dn\n",
         node->getFirstChild()->getGlobalIndex(), node->getSecondChild()->getGlobalIndex(), anchoredCallArg1TT->getNode()->getGlobalIndex(), anchoredCallArg2TT->getNode()->getGlobalIndex());
      }

   // put non-helper call in its own block by block splitting at the
   // next treetop and then at the current one
   TR::Block* prevBlock = tt->getEnclosingBlock();
   TR::Block* targetBlock = prevBlock->splitPostGRA(tt->getNextTreeTop(), cfg, true, NULL);

   // As the block is split after the helper call node, it is possible that as part of un-commoning
   // code to store nodes into registers or temp-slots is appended to the original block by the call
   // to splitPostGRA above.  Move the acmp helper call treetop to the end of prevBlock, along with
   // any stores resulting from un-commoning of the nodes in the helper call tree so that it can be
   // split into its own call block.
   TR::TreeTop* prevBlockExit = prevBlock->getExit();
   TR::TreeTop* iterTT = tt->getNextTreeTop();

   if (iterTT != prevBlockExit)
      {
      if (trace())
         {
         traceMsg(comp, "Moving treetop containing node n%dn [%p] for acmp helper call to end of prevBlock in preparation of final block split\n", tt->getNode()->getGlobalIndex(), tt->getNode());
         }

      // Remove TreeTop for call node, and gather it and the treetops for stores that
      // resulted from un-commoning in a TreeTop chain from tt to lastTTForCallBlock
      tt->unlink(false);
      TR::TreeTop* lastTTForCallBlock = tt;

      while (iterTT != prevBlockExit)
         {
         TR::TreeTop* nextTT = iterTT->getNextTreeTop();
         TR::ILOpCodes op = iterTT->getNode()->getOpCodeValue();

         if ((op == TR::iRegStore || op == TR::istore) && iterTT->getNode()->getFirstChild() == node)
            {
            if (trace())
               {
               traceMsg(comp, "Moving treetop containing node n%dn [%p] for store of acmp helper result to end of prevBlock in preparation of final block split\n", iterTT->getNode()->getGlobalIndex(), iterTT->getNode());
               }

            // Remove store node from prevBlock temporarily
            iterTT->unlink(false);
            lastTTForCallBlock->join(iterTT);
            lastTTForCallBlock = iterTT;
            }

         iterTT = nextTT;
         }

      // Move the treetops that were gathered for the call and any stores of the
      // result to the end of the block in preparation for the split of the call block
      prevBlockExit->getPrevTreeTop()->join(tt);
      lastTTForCallBlock->join(prevBlockExit);
      }

   TR::Block* callBlock = prevBlock->split(tt, cfg);
   callBlock->setIsExtensionOfPreviousBlock(true);
   if (trace())
      traceMsg(comp, "Isolated call node n%dn in block_%d\n", node->getGlobalIndex(), callBlock->getNumber());

   // insert store of constant 1
   // the value must go wherever the value returned by the helper call goes
   // so that the code in the target block picks up the constant if we fast-path
   // (i.e. jump around) the call
   TR::Node* anchoredNode = anchoredCallTT->getNode()->getFirstChild(); // call node is under a treetop node
   if (trace())
      traceMsg(comp, "Anchored call has been transformed into %s node n%dn\n", anchoredNode->getOpCode().getName(), anchoredNode->getGlobalIndex());
   auto* const1Node = TR::Node::iconst(1);
   TR::Node* storeNode = NULL;
   if (anchoredNode->getOpCodeValue() == TR::iRegLoad)
      {
      if (trace())
         traceMsg(comp, "Storing constant 1 in register %s\n", comp->getDebug()->getGlobalRegisterName(anchoredNode->getGlobalRegisterNumber()));
      storeNode = TR::Node::create(TR::iRegStore, 1, const1Node);
      storeNode->setGlobalRegisterNumber(anchoredNode->getGlobalRegisterNumber());
      }
   else if (anchoredNode->getOpCodeValue() == TR::iload)
      {
      if (trace())
         traceMsg(comp, "Storing constant 1 to symref %d (%s)\n", anchoredNode->getSymbolReference()->getReferenceNumber(), anchoredNode->getSymbolReference()->getName(comp->getDebug()));
      storeNode = TR::Node::create(TR::istore, 1, const1Node);
      storeNode->setSymbolReference(anchoredNode->getSymbolReference());
      }
   else
      TR_ASSERT_FATAL_WITH_NODE(anchoredNode, false, "Anchored call has been turned into unexpected opcode\n");
   prevBlock->append(TR::TreeTop::create(comp, storeNode));

   // insert acmpeq for fastpath, taking care to set the proper register dependencies
   // Any register dependencies added by splitPostGRA will now be on the BBExit for
   // the call block.  As the ifacmpeq branching around the call block will reach the same
   // target block, copy any GlRegDeps from the end of the call block to the ifacmpeq
   auto* ifacmpeqNode = TR::Node::createif(TR::ifacmpeq, anchoredCallArg1TT->getNode()->getFirstChild(), anchoredCallArg2TT->getNode()->getFirstChild(), targetBlock->getEntry());
   if (callBlock->getExit()->getNode()->getNumChildren() > 0)
      {
      TR::Node* glRegDeps = TR::Node::create(TR::GlRegDeps);
      TR::Node* depNode = NULL;

      if (anchoredNode->getOpCodeValue() == TR::iRegLoad)
         {
         depNode = TR::Node::create(TR::PassThrough, 1, storeNode->getChild(0));
         depNode->setGlobalRegisterNumber(storeNode->getGlobalRegisterNumber());
         glRegDeps->addChildren(&depNode, 1);
         }

      ifacmpeqNode->addChildren(&glRegDeps, 1);

      TR::Node* expectedDeps = callBlock->getExit()->getNode()->getFirstChild();
      for (int i = 0; i < expectedDeps->getNumChildren(); ++i)
         {
         TR::Node* temp = expectedDeps->getChild(i);
         if (depNode && temp->getGlobalRegisterNumber() == depNode->getGlobalRegisterNumber())
            continue;
         else if (temp->getOpCodeValue() == TR::PassThrough)
            {
            // PassThrough nodes cannot be commoned because doing so does not
            // actually anchor the child, causing it's lifetime to not be extended
            TR::Node* original = temp;
            temp = TR::Node::create(original, TR::PassThrough, 1, original->getFirstChild());
            temp->setLowGlobalRegisterNumber(original->getLowGlobalRegisterNumber());
            temp->setHighGlobalRegisterNumber(original->getHighGlobalRegisterNumber());
            }
         glRegDeps->addChildren(&temp, 1);
         }
      }

   prevBlock->append(TR::TreeTop::create(comp, ifacmpeqNode));
   cfg->addEdge(prevBlock, targetBlock);
   }

/**
 * If value types are enabled, and the value that is being assigned to the array
 * element might be a null reference, lower the ArrayStoreCHK by splitting the
 * block before the ArrayStoreCHK, and inserting a NULLCHK guarded by a check
 * of whether the array's component type is a value type.
 *
 * @param node is the current node in the tree walk
 * @param tt is the treetop at the root of the tree ancoring the current node
 */
void
TR::TreeLowering::lowerArrayStoreCHK(TR::Node *node, TR::TreeTop *tt)
   {
   // Pattern match the ArrayStoreCHK operands to get the source of the assignment
   // (sourceChild) and the array to which an element will have a value assigned (destChild)
   TR::Node *firstChild = node->getFirstChild();

   TR::Node *sourceChild = firstChild->getSecondChild();
   TR::Node *destChild = firstChild->getChild(2);

   // Only need to lower if it is possible that the value is a null reference
   if (!sourceChild->isNonNull())
      {
      TR::CFG * cfg = comp()->getFlowGraph();
      cfg->invalidateStructure();

      TR::Block *prevBlock = tt->getEnclosingBlock();

      performTransformation(comp(), "%sTransforming ArrayStoreCHK n%dn [%p] by splitting block block_%d, and inserting a NULLCHK guarded with a check of whether the component type of the array is a value type\n", optDetailString(), node->getGlobalIndex(), node, prevBlock->getNumber());

      // Anchor the node containing the source of the array element
      // assignment and the node that contains the destination array
      // to ensure they are available for the ificmpeq and NULLCHK
      TR::TreeTop *anchoredArrayTT = TR::TreeTop::create(comp(), tt->getPrevTreeTop(), TR::Node::create(TR::treetop, 1, destChild));
      TR::TreeTop *anchoredSourceTT = TR::TreeTop::create(comp(), anchoredArrayTT, TR::Node::create(TR::treetop, 1, sourceChild));

      // Transform
      //   +--------------------------------+
      //   | ttprev                         |
      //   | ArrayStoreCHK                  |
      //   |   astorei/awrtbari             |
      //   |     aladd                      |
      //   |       <array-reference>        |
      //   |       index-offset-calculation |
      //   |     <value-reference>          |
      //   +--------------------------------+
      //
      // into
      //   +--------------------------------+
      //   | treetop                        |
      //   |   <array-reference>            |
      //   | treetop                        |
      //   |   <value-reference>            |
      //   | ificmpeq  -->------------------*---------+
      //   |   iand                         |         |
      //   |     iloadi <isClassFlags>      |         |
      //   |       aloadi <componentClass>  |         |
      //   |         aloadi <vft-symbol>    |         |
      //   |           <array-reference>    |         |
      //   |     iconst J9ClassIsValueType  |         |
      //   |   iconst 0                     |         |
      //   | BBEnd                          |         |
      //   +--------------------------------+         |
      //   | BBStart (Extension)            |         |
      //   | NULLCHK                        |         |
      //   |   Passthrough                  |         |
      //   |     <value-reference>          |         |
      //   | BBEnd                          |         |
      //   +--------------------------------+         |
      //                   |                          |
      //                   +--------------------------+
      //                   |
      //                   v
      //   +--------------------------------+
      //   | BBStart                        |
      //   | ArrayStoreCHK                  |
      //   |   astorei/awrtbari             |
      //   |     aladd                      |
      //   |       aload <array>            |
      //   |       index-offset-calculation |
      //   |     aload <value>              |
      //   +--------------------------------+
      //
      TR::SymbolReference *vftSymRef = comp()->getSymRefTab()->findOrCreateVftSymbolRef();
      TR::SymbolReference *arrayCompSymRef = comp()->getSymRefTab()->findOrCreateArrayComponentTypeSymbolRef();
      TR::SymbolReference *classFlagsSymRef = comp()->getSymRefTab()->findOrCreateClassFlagsSymbolRef();

      TR::Node *vft = TR::Node::createWithSymRef(node, TR::aloadi, 1, anchoredArrayTT->getNode()->getFirstChild(), vftSymRef);
      TR::Node *arrayCompClass = TR::Node::createWithSymRef(node, TR::aloadi, 1, vft, arrayCompSymRef);
      TR::Node *loadClassFlags = TR::Node::createWithSymRef(node, TR::iloadi, 1, arrayCompClass, classFlagsSymRef);
      TR::Node *isValueTypeNode = TR::Node::create(node, TR::iand, 2, loadClassFlags, TR::Node::iconst(node, J9ClassIsValueType));

      TR::Node *ifNode = TR::Node::createif(TR::ificmpeq, isValueTypeNode, TR::Node::iconst(node, 0));
      ifNode->copyByteCodeInfo(node);

      TR::Node *passThru  = TR::Node::create(node, TR::PassThrough, 1, sourceChild);
      TR::ResolvedMethodSymbol *currentMethod = comp()->getMethodSymbol();

      TR::Block *arrayStoreCheckBlock = prevBlock->splitPostGRA(tt, cfg);

      ifNode->setBranchDestination(arrayStoreCheckBlock->getEntry());

      // Copy register dependencies from the end of the block split before the
      // ArrayStoreCHK to the ificmpeq that's being added to the end of that block
      if (prevBlock->getExit()->getNode()->getNumChildren() != 0)
         {
         TR::Node *blkDeps = prevBlock->getExit()->getNode()->getFirstChild();
         TR::Node *ifDeps = TR::Node::create(blkDeps, TR::GlRegDeps);

         for (int i = 0; i < blkDeps->getNumChildren(); i++)
            {
            TR::Node *regDep = blkDeps->getChild(i);

            if (regDep->getOpCodeValue() == TR::PassThrough)
               {
               TR::Node *orig= regDep;
               regDep = TR::Node::create(orig, TR::PassThrough, 1, orig->getFirstChild());
               regDep->setLowGlobalRegisterNumber(orig->getLowGlobalRegisterNumber());
               regDep->setHighGlobalRegisterNumber(orig->getHighGlobalRegisterNumber());
               }

            ifDeps->addChildren(&regDep, 1);
            }

         ifNode->addChildren(&ifDeps, 1);
         }

      prevBlock->append(TR::TreeTop::create(comp(), ifNode));

      TR::Node *nullCheck = TR::Node::createWithSymRef(node, TR::NULLCHK, 1, passThru,
                               comp()->getSymRefTab()->findOrCreateNullCheckSymbolRef(currentMethod));
      TR::TreeTop *nullCheckTT = prevBlock->append(TR::TreeTop::create(comp(), nullCheck));

      TR::Block *nullCheckBlock = prevBlock->split(nullCheckTT, cfg);

      nullCheckBlock->setIsExtensionOfPreviousBlock(true);

      cfg->addEdge(prevBlock, arrayStoreCheckBlock);
      }
   }

static TR::Node *
saveGlRegDepsFromBBExit(TR::Node *bbExitNode, TR::Compilation *comp, bool enableTrace, TR_GlobalRegisterNumber registerToSkip = -1)
   {
   TR::Node *tmpGlRegDeps = NULL;
   if (bbExitNode->getNumChildren() > 0)
      {
      TR::Node *origRegDeps = bbExitNode->getFirstChild();
      tmpGlRegDeps = TR::Node::create(origRegDeps, TR::GlRegDeps);

      for (int32_t i=0; i < origRegDeps->getNumChildren(); ++i)
         {
         TR::Node *regDep = origRegDeps->getChild(i);

         if ((registerToSkip != -1) &&
             regDep->getOpCodeValue() == TR::PassThrough &&
             regDep->getGlobalRegisterNumber() == registerToSkip) // TODO: AHUO check highRegisters?
            {
            if (enableTrace)
               traceMsg(comp,"tmpGlRegDeps skip n%dn [%d] %s %s\n",
                     regDep->getGlobalIndex(), i, regDep->getOpCode().getName(), comp->getDebug()->getGlobalRegisterName(regDep->getGlobalRegisterNumber()));
            continue;
            }
         else
            {
            if (enableTrace)
               traceMsg(comp,"tmpGlRegDeps add n%dn [%d] %s %s\n",
                     regDep->getGlobalIndex(), i, regDep->getOpCode().getName(), comp->getDebug()->getGlobalRegisterName(regDep->getGlobalRegisterNumber()));
            }

         if (regDep->getOpCodeValue() == TR::PassThrough)
            {
            TR::Node *orig = regDep;
            regDep = TR::Node::create(orig, TR::PassThrough, 1, orig->getFirstChild());
            regDep->setLowGlobalRegisterNumber(orig->getLowGlobalRegisterNumber());
            regDep->setHighGlobalRegisterNumber(orig->getHighGlobalRegisterNumber());
            }

         tmpGlRegDeps->addChildren(&regDep, 1);
         }
      }

   return tmpGlRegDeps;
   }

static TR::Node *
createStoreNodeForAnchoredNode(TR::Node *anchoredNode, TR::Node *nodeToBeStored, const char *msg, TR::Compilation *comp, bool enableTrace)
   {
   TR::Node *storeNode = NULL;

   // After splitPostGRA anchoredNode which was the helper call node
   // should have been transformed into a aRegLoad or aload
   if (anchoredNode->getOpCodeValue() == TR::aRegLoad)
      {
      storeNode = TR::Node::create(TR::aRegStore, 1, nodeToBeStored);
      storeNode->setGlobalRegisterNumber(anchoredNode->getGlobalRegisterNumber());
      if (enableTrace)
         traceMsg(comp, "Storing %s n%dn in register %s storeNode n%dn anchoredNode n%dn\n", msg, nodeToBeStored->getGlobalIndex(), comp->getDebug()->getGlobalRegisterName(anchoredNode->getGlobalRegisterNumber()), storeNode->getGlobalIndex(), anchoredNode->getGlobalIndex());
      }
   else if (anchoredNode->getOpCodeValue() == TR::aload)
      {
      storeNode = TR::Node::create(TR::astore, 1, nodeToBeStored);
      storeNode->setSymbolReference(anchoredNode->getSymbolReference());
      if (enableTrace)
         traceMsg(comp, "Storing %s n%dn to symref %d (%s) storeNode n%dn anchoredNode n%dn\n", msg, nodeToBeStored->getGlobalIndex(), anchoredNode->getSymbolReference()->getReferenceNumber(), anchoredNode->getSymbolReference()->getName(comp->getDebug()), storeNode->getGlobalIndex(), anchoredNode->getGlobalIndex());
      }
   else
      {
      TR_ASSERT_FATAL_WITH_NODE(anchoredNode, false, "Anchored call node n%dn has been turned into unexpected opcode\n",
                                anchoredNode->getGlobalIndex());
      }

   return storeNode;
   }

static void
copyRegisterDependency(TR::Node *fromNode, TR::Node *toNode)
   {
   if (fromNode->getNumChildren() != 0)
      {
      TR::Node *blkDeps = fromNode->getFirstChild();
      TR::Node *newDeps = TR::Node::create(blkDeps, TR::GlRegDeps);

      for (int i = 0; i < blkDeps->getNumChildren(); i++)
         {
         TR::Node *regDep = blkDeps->getChild(i);

         if (regDep->getOpCodeValue() == TR::PassThrough)
            {
            TR::Node *orig= regDep;
            regDep = TR::Node::create(orig, TR::PassThrough, 1, orig->getFirstChild());
            regDep->setLowGlobalRegisterNumber(orig->getLowGlobalRegisterNumber());
            regDep->setHighGlobalRegisterNumber(orig->getHighGlobalRegisterNumber());
            }

         newDeps->addChildren(&regDep, 1);
         }

      toNode->addChildren(&newDeps, 1);
      }
   }

//TODO: to be removed
TR::Node *
testIsClassValueType(TR::Node *j9ClassRefNode, TR::Compilation *comp)
   {
   TR::SymbolReference *classFlagsSymRef = comp->getSymRefTab()->findOrCreateClassFlagsSymbolRef();

   TR::Node *loadClassFlags = TR::Node::createWithSymRef(TR::iloadi, 1, 1, j9ClassRefNode, classFlagsSymRef);
   TR::Node *isValueTypeNode = TR::Node::create(TR::iand, 2, loadClassFlags, TR::Node::iconst(j9ClassRefNode, J9ClassIsValueType));

   return isValueTypeNode;
   }

/*
 * lowerLoadArrayElement transforms the block that contains the jitLoadFlattenableArrayElement helper call into three blocks:
 *   1. The merge block (blockAfterHelperCall) that contains the tree tops after the helper call
 *   2. The helper call block (helperCallBlock) that contains the helper call and is moved to the end of the tree top list
 *   3. The new non-VT array load block (arrayElementLoadBlock) which is an extended block of the original block
 *
 *      originalBlock----------+
 *      arrayElementLoadBlock  |
 *              |              |
 *              |              v
 *              |       helperCallBlock
 *              |              |
 *              v              v
 *            blockAfterHelperCall
 *
 *
 +----------------------------------------+
 |treetop                                 |
 |  acall  jitLoadFlattenableArrayElement |
 |     ==>iRegLoad                        |
 |     ==>aRegLoad                        |
 |ttAfterHelperCall                       |
 +----------------------------------------+
              |           |
              v           v

 +------------------------------------------+
 |BBStart                                   |
 |treetop                                   |
 |   ==>iRegLoad                            |
 |treetop                                   |
 |   ==>aRegLoad                            |
 |ificmpne ----->---------------------------+-----------+
 |   iand                                   |           |
 |      iloadi  <isClassFlags>              |           |
 |      ...                                 |           |
 |      iconst 1024                         |           |
 |   iconst 0                               |           |
 |   GlRegDeps ()                           |           |
 |      ==>aRegLoad                         |           |
 |      ==>iRegLoad                         |           |
 |BBEnd                                     |           |
 +------------------------------------------+           |
 +------------------------------------------+           |
 |BBStart (extension of previous block)     |           |
 |NULLCHK on n191n                          |           |
 |   arraylength (stride 8)                 |           |
 |      ==>aRegLoad                         |           |
 |BNDCHK                                    |           |
 |   ==>arraylength                         |           |
 |   ==>iRegLoad                            |           |
 |compressedRefs                            |           |
 |   aloadi                                 |           |
 |      aladd                               |           |
 |        ...                               |           |
 |   lconst 0                               |           |
 |aRegStore edi                             |           |
 |   ==>aloadi                              |           |
 |BBEnd                                     |           |
 |   GlRegDeps ()                           |           |
 |      PassThrough rdi                     |           |
 |         ==>aloadi                        |           |
 |      ==>aRegLoad                         |           |
 |      ==>iRegLoad                         |           |
 +---------------------+--------------------+           |
                       |                                |
                       +----------------------------+   |
                       |                            |   |
 +---------------------v--------------------+       |   |
 |BBStart                                   |       |   |
 |   GlRegDeps ()                           |       |   |
 |      aRegLoad r9d                        |       |   |
 |      iRegLoad ebx                        |       |   |
 |      aRegLoad edi                        |       |   |
 |treetop                                   |       |   |
 |   ==>aRegLoad                            |       |   |
 |ttAfterHelperCall                         |       |   |
 +------------------------------------------+       |   |
                                                    |   |
                       +----------------------------|---+
                       |                            |
                       |                            |
 +---------------------v---------------------+      |
 |BBStart                                    |      |
 |   GlRegDeps ()                            |      |
 |   ==>aRegLoad                             |      |
 |   ==>iRegLoad                             |      |
 |treetop                                    |      |
 |   acall  jitLoadFlattenableArrayElement   |      |
 |      ==>iRegLoad                          |      |
 |      ==>aRegLoad                          |      |
 |aRegStore edi                              |      |
 |    ==>acall                               |      |
 |goto  ----->-------------------------------+------+
 |   GlRegDeps ()                            |
 |      ==>aRegLoad                          |
 |      ==>iRegLoad                          |
 |      PassThrough rdi                      |
 |         ==>acall                          |
 |BBEnd                                      |
 +-------------------------------------------+
 *
 */
void
TR::TreeLowering::lowerLoadArrayElement(TR::PreorderNodeIterator& nodeIter, TR::Node *node, TR::TreeTop *tt)
   {
   bool enableTrace = trace();
   TR::Compilation *comp = self()->comp();
   TR::Block *originalBlock = tt->getEnclosingBlock();
   TR::Node *elementIndexNode = node->getFirstChild();
   TR::Node *arrayBaseAddressNode = node->getSecondChild();

   if (!performTransformation(comp, "%sTransforming loadArrayElement treetop n%dn node n%dn [%p] in block_%d: elementIndexNode n%dn arrayBaseAddressNode n%dn ttAfterHelperCall n%dn\n", optDetailString(),
          tt->getNode()->getGlobalIndex(), node->getGlobalIndex(), node, originalBlock->getNumber(),
          elementIndexNode->getGlobalIndex(), arrayBaseAddressNode->getGlobalIndex(), tt->getNextTreeTop()->getNode()->getGlobalIndex()))
      return;

   TR::CFG *cfg = comp->getFlowGraph();
   cfg->invalidateStructure();

   ///////////////////////////////////////
   // 1. Anchor helper call node after the helper call
   //    Anchor elementIndex and arrayBaseAddress before the helper call

   // Anchoring the helper call ensures that the return value from the helper call or from the non-VT array element load
   // will be saved to a register or a temp.
   TR::TreeTop *anchoredCallTT = TR::TreeTop::create(comp, tt, TR::Node::create(TR::treetop, 1, node));
   TR::TreeTop *anchoredElementIndexTT = TR::TreeTop::create(comp, tt->getPrevTreeTop(), TR::Node::create(TR::treetop, 1, elementIndexNode));
   TR::TreeTop *anchoredArrayBaseAddressTT = TR::TreeTop::create(comp, anchoredElementIndexTT, TR::Node::create(TR::treetop, 1, arrayBaseAddressNode));

   if (enableTrace)
      traceMsg(comp, "Anchored call node under treetop n%un (0x%p), elementIndex under treetop n%un (0x%p), arrayBaseAddress under treetop n%un (0x%p)\n",
            anchoredCallTT->getNode()->getGlobalIndex(), anchoredCallTT->getNode(),
            anchoredElementIndexTT->getNode()->getGlobalIndex(), anchoredElementIndexTT->getNode(),
            anchoredArrayBaseAddressTT->getNode()->getGlobalIndex(), anchoredArrayBaseAddressTT->getNode());


   ///////////////////////////////////////
   // 2. Split (1) after the helper call
   TR::Block *blockAfterHelperCall = originalBlock->splitPostGRA(anchoredCallTT, cfg, true, NULL);

   if (enableTrace)
      traceMsg(comp, "Isolated the anchored call treetop n%dn in block_%d\n", anchoredCallTT->getNode()->getGlobalIndex(), blockAfterHelperCall->getNumber());


   ///////////////////////////////////////
   // 3. Save the GlRegDeps of the originalBlock's BBExit
   //
   // The GlRegDeps for the BBExit of the originalBlock after the first split is what is required for
   // the BBExit of arrayElementLoadBlock. It has to be saved because it might get changed after the next split at the helper call.
   //
   // If the anchoredNode is saved to a register, there is a PassThrough for the return value from
   // the helper call. It should not be copied here, otherwise the helper call will get moved up to
   // the GlRegDeps of arrayElementLoadBlock BBExit due to un-commoning in split.
   TR::Node *anchoredNode = anchoredCallTT->getNode()->getFirstChild();
   TR_GlobalRegisterNumber registerToSkip = (anchoredNode->getOpCodeValue() == TR::aRegLoad) ? anchoredNode->getGlobalRegisterNumber() : -1;
   TR::Node *tmpGlRegDeps = saveGlRegDepsFromBBExit(originalBlock->getExit()->getNode(), comp, enableTrace, registerToSkip);


   ///////////////////////////////////////
   // 4. Move the helper call and the aRegStore/astore of the call (if exist) to the end of the block before next split
   moveNodeToEndOfBlock(originalBlock, tt, node, true /* isAddress */);


   ///////////////////////////////////////
   // 5. Split (2) at the helper call
   TR::Block *helperCallBlock = originalBlock->splitPostGRA(tt, cfg, true, NULL);

   if (enableTrace)
      traceMsg(comp, "Isolated helper call treetop n%dn node n%dn in block_%d\n", tt->getNode()->getGlobalIndex(), node->getGlobalIndex(), helperCallBlock->getNumber());


   ///////////////////////////////////////
   // 6. Create array element load node and append to the originalBlock
   TR::Node *anchoredArrayBaseAddressNode = anchoredArrayBaseAddressTT->getNode()->getFirstChild();
   TR::Node *anchoredElementIndexNode = anchoredElementIndexTT->getNode()->getFirstChild();

   TR::Node *elementAddress = J9::TransformUtil::calculateElementAddress(comp, anchoredArrayBaseAddressNode, anchoredElementIndexNode, TR::Address);
   TR::SymbolReference *elementSymRef = comp->getSymRefTab()->findOrCreateArrayShadowSymbolRef(TR::Address, anchoredArrayBaseAddressNode);
   TR::Node *elementLoadNode = TR::Node::createWithSymRef(comp->il.opCodeForIndirectArrayLoad(TR::Address), 1, 1, elementAddress, elementSymRef);
   elementLoadNode->copyByteCodeInfo(node);

   TR::TreeTop *elementLoadTT = NULL;
   if (comp->useCompressedPointers())
      elementLoadTT = originalBlock->append(TR::TreeTop::create(comp, TR::Node::createCompressedRefsAnchor(elementLoadNode)));
   else
      elementLoadTT = originalBlock->append(TR::TreeTop::create(comp, TR::Node::create(node, TR::treetop, 1, elementLoadNode)));

   if (enableTrace)
      traceMsg(comp, "Created array element load treetop n%dn node n%dn\n", elementLoadTT->getNode()->getGlobalIndex(), elementLoadNode->getGlobalIndex());


   ///////////////////////////////////////
   // 7. Store the return value from the array element load to the same register or temp used by the anchored node
   TR::Node *storeArrayElementNode = createStoreNodeForAnchoredNode(anchoredNode, elementLoadNode, "array element load", comp, enableTrace);

   elementLoadTT->insertAfter(TR::TreeTop::create(comp, storeArrayElementNode));

   if (enableTrace)
      traceMsg(comp, "Store array element load node n%dn to n%dn %s\n", elementLoadNode->getGlobalIndex(), storeArrayElementNode->getGlobalIndex(), storeArrayElementNode->getOpCode().getName());


   ///////////////////////////////////////
   // 8. Split (3) at the array element load node
   TR::Block *arrayElementLoadBlock = originalBlock->split(elementLoadTT, cfg);

   arrayElementLoadBlock->setIsExtensionOfPreviousBlock(true);

   if (enableTrace)
      traceMsg(comp, "Isolated array element load treetop n%dn node n%dn in block_%d\n", elementLoadTT->getNode()->getGlobalIndex(), elementLoadNode->getGlobalIndex(), arrayElementLoadBlock->getNumber());

   int32_t dataWidth = TR::Symbol::convertTypeToSize(TR::Address);
   if (comp->useCompressedPointers())
      dataWidth = TR::Compiler->om.sizeofReferenceField();

   TR::Node *arraylengthNode = TR::Node::create(TR::arraylength, 1, anchoredArrayBaseAddressNode);
   arraylengthNode->setArrayStride(dataWidth);

   elementLoadTT->insertBefore(TR::TreeTop::create(comp, TR::Node::createWithSymRef(TR::NULLCHK, 1, 1, arraylengthNode, comp->getSymRefTab()->findOrCreateNullCheckSymbolRef(comp->getMethodSymbol()))));

   elementLoadTT->insertBefore(TR::TreeTop::create(comp, TR::Node::createWithSymRef(TR::BNDCHK, 2, 2, arraylengthNode, anchoredElementIndexNode, comp->getSymRefTab()->findOrCreateArrayBoundsCheckSymbolRef(comp->getMethodSymbol()))));


   ///////////////////////////////////////
   // 9. Create ificmpne node that checks classFlags
   TR::SymbolReference *vftSymRef = comp->getSymRefTab()->findOrCreateVftSymbolRef();
   TR::SymbolReference *arrayCompSymRef = comp->getSymRefTab()->findOrCreateArrayComponentTypeSymbolRef();
   TR::SymbolReference *classFlagsSymRef = comp->getSymRefTab()->findOrCreateClassFlagsSymbolRef();

   TR::Node *vft = TR::Node::createWithSymRef(node, TR::aloadi, 1, anchoredArrayBaseAddressNode, vftSymRef);
   TR::Node *arrayCompClass = TR::Node::createWithSymRef(node, TR::aloadi, 1, vft, arrayCompSymRef);
   //TR::Node *testIsValueTypeNode = comp()->fej9()->testIsClassValueType(arrayCompClass);
   TR::Node *testIsValueTypeNode = testIsClassValueType(arrayCompClass, comp);

   // The branch destination will be set up later
   TR::Node *ifNode = TR::Node::createif(TR::ificmpne, testIsValueTypeNode, TR::Node::iconst(node, 0));

   // Copy register dependency to the ificmpne node that's being appended to the current block
   copyRegisterDependency(arrayElementLoadBlock->getExit()->getNode(), ifNode);

   // Append the ificmpne node that checks classFlags to the original block
   originalBlock->append(TR::TreeTop::create(comp, ifNode));

   if (enableTrace)
      traceMsg(comp, "Append ifNode n%dn to block_%d\n", ifNode->getGlobalIndex(), originalBlock->getNumber());


   ///////////////////////////////////////
   // 10. Copy tmpGlRegDeps to arrayElementLoadBlock

   // Adjust the reference count of the GlRegDeps of the BBExit since it will be replaced by
   // the previously saved tmpGlRegDeps
   if (arrayElementLoadBlock->getExit()->getNode()->getNumChildren() > 0)
      {
      TR::Node *origRegDeps = arrayElementLoadBlock->getExit()->getNode()->getFirstChild();
      prepareToReplaceNode(origRegDeps);
      origRegDeps->decReferenceCount();
      arrayElementLoadBlock->getExit()->getNode()->setNumChildren(0);
      }

   if (tmpGlRegDeps)
      {
      arrayElementLoadBlock->getExit()->getNode()->setNumChildren(1);
      arrayElementLoadBlock->getExit()->getNode()->setAndIncChild(0, tmpGlRegDeps);
      }

   // Add storeArrayElementNode to GlRegDeps to pass the return value from the array element load to blockAfterHelperCall
   if (storeArrayElementNode->getOpCodeValue() == TR::aRegStore)
      {
      TR::Node *blkDeps = arrayElementLoadBlock->getExit()->getNode()->getFirstChild();

      TR::Node *depNode = TR::Node::create(TR::PassThrough, 1, storeArrayElementNode->getChild(0));
      depNode->setGlobalRegisterNumber(storeArrayElementNode->getGlobalRegisterNumber());
      blkDeps->addChildren(&depNode, 1);
      }


   ///////////////////////////////////////
   // 11. Set up the edges between the blocks
   ifNode->setBranchDestination(helperCallBlock->getEntry());

   cfg->addEdge(originalBlock, helperCallBlock);

   cfg->removeEdge(arrayElementLoadBlock, helperCallBlock);
   cfg->addEdge(arrayElementLoadBlock, blockAfterHelperCall);

   // Force nodeIter to first TreeTop of next block so that
   // moving callBlock won't cause problems while iterating
   while (nodeIter.currentTree() != blockAfterHelperCall->getEntry())
       ++nodeIter;

   // Move helper call to the end of the tree list
   arrayElementLoadBlock->getExit()->join(blockAfterHelperCall->getEntry());

   TR::TreeTop *lastTreeTop = comp->getMethodSymbol()->getLastTreeTop();
   lastTreeTop->insertTreeTopsAfterMe(helperCallBlock->getEntry(), helperCallBlock->getExit());

   // Add Goto from the helper call to the merge block
   TR::Node *gotoAfterHelperCallNode = TR::Node::create(helperCallBlock->getExit()->getNode(), TR::Goto, 0, blockAfterHelperCall->getEntry());
   helperCallBlock->append(TR::TreeTop::create(comp, gotoAfterHelperCallNode));

   if (helperCallBlock->getExit()->getNode()->getNumChildren() > 0)
      {
      TR::Node *deps = helperCallBlock->getExit()->getNode()->getChild(0);
      helperCallBlock->getExit()->getNode()->setNumChildren(0);
      deps->decReferenceCount();
      gotoAfterHelperCallNode->addChildren(&deps, 1);
      }
   }

/*
 * lowerStoreArrayElement transforms the block that contains the jitStoreFlattenableArrayElement helper call into three blocks:
 *   1. The merge block that contains the tree tops after the helper call
 *   2. The helper call block that contains the helper call and is moved to the end of the tree top list
 *   3. The new non-VT array store block which is an extended block of the original block
 *
 *      originalBlock ----------+
 *      arrayElementStoreBlock  |
 *               |              |
 *               |              v
 *               |       helperCallBlock
 *               |              |
 *               v              v
 *             blockAfterHelperCall
 *
 +-------------------------------------------+
 |treetop                                    |
 |   acall  jitStoreFlattenableArrayElement  |
 |      aload <value>                        |
 |      iload <index>                        |
 |      aload <arrayAddress>                 |
 |ttAfterHelperCall                          |
 +-------------------------------------------+
               |              |
               v              v
 +-------------------------------------------+
 |BBStart                                    |
 |treetop                                    |
 |   aload <ArrayAddress>                    |
 |treetop                                    |
 |   aload <index>                           |
 |treetop                                    |
 |   aload <value>                           |
 |ificmpne ------>---------------------------+---------------+
 |   iand                                    |               |
 |      iloadi  <isClassFlags>               |               |
 |      ...                                  |               |
 |      iconst 1024                          |               |
 |   iconst 0                                |               |
 |   GlRegDeps ()                            |               |
 |      PassThrough rcx                      |               |
 |         ==>aload                          |               |
 |      PassThrough r8                       |               |
 |         ==>aload                          |               |
 |      PassThrough rdi                      |               |
 |         ==>iload                          |               |
 |BBEnd                                      |               |
 +-------------------------------------------+               |
 +-------------------------------------------+               |
 |BBStart (extension of previous block)      |               |
 |NULLCHK on n82n                            |               |
 |   ...                                     |               |
 |BNDCHK                                     |               |
 |   ...                                     |               |
 |treetop                                    |               |
 |   ArrayStoreCHK                           |               |
 |      awrtbari                             |               |
 |      ...                                  |               |
 |BBEnd                                      |               |
 |   GlRegDeps ()                            |               |
 |      PassThrough rcx                      |               |
 |         ==>aload                          |               |
 |      PassThrough r8                       |               |
 |         ==>aload                          |               |
 |      PassThrough rdi                      |               |
 |         ==>iload                          |               |
 +---------------------+---------------------+               |
                       |                                     |
                       +---------------------------+         |
                       |                           |         |
                       |                           |         |
 +---------------------v---------------------+     |         |
 |BBStart                                    |     |         |
 |   GlRegDeps ()                            |     |         |
 |      aRegLoad ecx                         |     |         |
 |      aRegLoad r8d                         |     |         |
 |      iRegLoad edi                         |     |         |
 |ttAfterArrayElementStore                   |     |         |
 +-------------------------------------------+     |         |
                                                   |         |
                       +---------------------------|---------+
                       |                           |
 +---------------------v---------------------+     |
 |BBStart                                    |     |
 |   GlRegDeps ()                            |     |
 |      aRegLoad ecx                         |     |
 |      aRegLoad r8d                         |     |
 |      iRegLoad edi                         |     |
 |NULLCHK                                    |     |
 |   PassThrough                             |     |
 |      ==>aload                             |     |
 |treetop                                    |     |
 |   acall  jitStoreFlattenableArrayElement  |     |
 |      ==>aRegLoad                          |     |
 |      ==>iRegLoad                          |     |
 |      ==>aRegLoad                          |     |
 |goto  ------->-----------------------------+-----+
 |   GlRegDeps ()                            |
 |      PassThrough rcx                      |
 |         ==>aload                          |
 |      PassThrough r8                       |
 |         ==>aload                          |
 |      PassThrough rdi                      |
 |         ==>iload                          |
 |BBEnd                                      |
 +-------------------------------------------+
 *
 */
void
TR::TreeLowering::lowerStoreArrayElement(TR::PreorderNodeIterator& nodeIter, TR::Node *node, TR::TreeTop *tt)
   {
   bool enableTrace = trace();
   TR::Compilation *comp = self()->comp();
   TR::Block *originalBlock = tt->getEnclosingBlock();

   TR::Node *valueNode = node->getFirstChild();
   TR::Node *elementIndexNode = node->getSecondChild();
   TR::Node *arrayBaseAddressNode = node->getThirdChild();

   if (!performTransformation(comp, "%sTransforming storeArrayElement treetop n%dn node n%dn [%p] in block_%d: children (n%dn, n%dn, n%dn) ttAfterHelperCall n%dn\n", optDetailString(), tt->getNode()->getGlobalIndex(), node->getGlobalIndex(), node, originalBlock->getNumber(),
          valueNode->getGlobalIndex(), elementIndexNode->getGlobalIndex(), arrayBaseAddressNode->getGlobalIndex(), tt->getNextTreeTop()->getNode()->getGlobalIndex()))
      return;

   TR::CFG *cfg = comp->getFlowGraph();
   cfg->invalidateStructure();


   ///////////////////////////////////////
   // 1. Anchor all the children nodes before the helper call
   TR::TreeTop *anchoredArrayBaseAddressTT = TR::TreeTop::create(comp, tt->getPrevTreeTop(), TR::Node::create(TR::treetop, 1, arrayBaseAddressNode));
   TR::TreeTop *anchoredElementIndexTT = TR::TreeTop::create(comp, anchoredArrayBaseAddressTT, TR::Node::create(TR::treetop, 1, elementIndexNode));
   TR::TreeTop *anchoredValueTT = TR::TreeTop::create(comp, anchoredElementIndexTT, TR::Node::create(TR::treetop, 1, valueNode));

   if (enableTrace)
      traceMsg(comp, "Anchored elementIndex under treetop n%un (0x%p), arrayBaseAddress under treetop n%un (0x%p), value under treetop n%un (0x%p), \n",
            anchoredElementIndexTT->getNode()->getGlobalIndex(), anchoredElementIndexTT->getNode(),
            anchoredArrayBaseAddressTT->getNode()->getGlobalIndex(), anchoredArrayBaseAddressTT->getNode(),
            anchoredValueTT->getNode()->getGlobalIndex(), anchoredValueTT->getNode());


   ///////////////////////////////////////
   // 2. Split (1) after the helper call
   TR::Block *blockAfterHelperCall = originalBlock->splitPostGRA(tt->getNextTreeTop(), cfg, true, NULL);

   if (enableTrace)
      traceMsg(comp, "Isolated the trees after the helper call in block_%d\n", blockAfterHelperCall->getNumber());


   ///////////////////////////////////////
   // 3. Save the GlRegDeps of the originalBlock's BBExit
   TR::Node *tmpGlRegDeps = saveGlRegDepsFromBBExit(originalBlock->getExit()->getNode(), comp, -1 /* registerToSkip */);


   ///////////////////////////////////////
   // 4. Move the helper call node to the end of the originalBlock
   TR::TreeTop *originalBlockExit = originalBlock->getExit();
   if (tt->getNextTreeTop() != originalBlockExit)
      {
      tt->unlink(false);
      originalBlockExit->getPrevTreeTop()->join(tt);
      tt->join(originalBlockExit);
      }


   ///////////////////////////////////////
   // 5. Split (2) at the helper call node including the nullchk on the value reference into its own helperCallBlock

   // Insert NULLCHK for VT
   TR::Node *anchoredValueNode = anchoredValueTT->getNode()->getFirstChild();
   TR::TreeTop *ttForHelperCallBlock = tt;

   if (!anchoredValueNode->isNonNull())
      {
      TR::Node *passThru  = TR::Node::create(node, TR::PassThrough, 1, anchoredValueNode);
      TR::Node *nullCheck = TR::Node::createWithSymRef(node, TR::NULLCHK, 1, passThru, comp->getSymRefTab()->findOrCreateNullCheckSymbolRef(comp->getMethodSymbol()));
      ttForHelperCallBlock = tt->insertBefore(TR::TreeTop::create(comp, nullCheck));
      }

   TR::Block *helperCallBlock = originalBlock->splitPostGRA(ttForHelperCallBlock, cfg, true, NULL);

   if (enableTrace)
      traceMsg(comp, "Isolated helper call treetop n%dn node n%dn in block_%d\n", tt->getNode()->getGlobalIndex(), node->getGlobalIndex(), helperCallBlock->getNumber());


   ///////////////////////////////////////
   // 6. Create the new ArrayStoreCHK
   TR::Node *anchoredElementIndexNode = anchoredElementIndexTT->getNode()->getFirstChild();
   TR::Node *anchoredArrayBaseAddressNode = anchoredArrayBaseAddressTT->getNode()->getFirstChild();

   TR::Node *elementAddress = J9::TransformUtil::calculateElementAddress(comp, anchoredArrayBaseAddressNode, anchoredElementIndexNode, TR::Address);

   TR::SymbolReference *elementSymRef = comp->getSymRefTab()->findOrCreateArrayShadowSymbolRef(TR::Address, anchoredArrayBaseAddressNode);
   TR::Node *elementStoreNode = TR::Node::createWithSymRef(TR::awrtbari, 3, 3, elementAddress, anchoredValueNode, anchoredArrayBaseAddressNode, elementSymRef);

   TR::SymbolReference *arrayStoreCHKSymRef = comp->getSymRefTab()->findOrCreateTypeCheckArrayStoreSymbolRef(comp->getMethodSymbol());
   TR::Node *arrayStoreCHKNode = TR::Node::createWithRoomForThree(TR::ArrayStoreCHK, elementStoreNode, 0, arrayStoreCHKSymRef);
   arrayStoreCHKNode->copyByteCodeInfo(node);

   TR::TreeTop *arrayStoreCHKTT = originalBlock->append(TR::TreeTop::create(comp, arrayStoreCHKNode));

   if (enableTrace)
      traceMsg(comp, "Created arrayStoreCHK treetop n%dn node n%dn\n", arrayStoreCHKTT->getNode()->getGlobalIndex(), arrayStoreCHKNode->getGlobalIndex());


   ///////////////////////////////////////
   // 7. Split (3) at the regular array element store
   TR::Block *arrayElementStoreBlock = originalBlock->split(arrayStoreCHKTT, cfg);

   arrayElementStoreBlock->setIsExtensionOfPreviousBlock(true);

   if (enableTrace)
      traceMsg(comp, "Isolated array element store treetop n%dn node n%dn in block_%d\n", arrayStoreCHKTT->getNode()->getGlobalIndex(), arrayStoreCHKNode->getGlobalIndex(), arrayElementStoreBlock->getNumber());

   int32_t dataWidth = TR::Symbol::convertTypeToSize(TR::Address);
   if (comp->useCompressedPointers())
      dataWidth = TR::Compiler->om.sizeofReferenceField();

   TR::Node *arraylengthNode = TR::Node::create(TR::arraylength, 1, anchoredArrayBaseAddressNode);
   arraylengthNode->setArrayStride(dataWidth);

   arrayStoreCHKTT->insertBefore(TR::TreeTop::create(comp, TR::Node::createWithSymRef(TR::NULLCHK, 1, 1, arraylengthNode, comp->getSymRefTab()->findOrCreateNullCheckSymbolRef(comp->getMethodSymbol()))));

   arrayStoreCHKTT->insertBefore(TR::TreeTop::create(comp, TR::Node::createWithSymRef(TR::BNDCHK, 2, 2, arraylengthNode, anchoredElementIndexNode, comp->getSymRefTab()->findOrCreateArrayBoundsCheckSymbolRef(comp->getMethodSymbol()))));

   if (comp->useCompressedPointers())
      {
      arrayStoreCHKTT->insertAfter(TR::TreeTop::create(comp, TR::Node::createCompressedRefsAnchor(elementStoreNode)));
      }


   ///////////////////////////////////////
   // 8. Create the ificmpne node that checks classFlags
   TR::SymbolReference *vftSymRef = comp->getSymRefTab()->findOrCreateVftSymbolRef();
   TR::SymbolReference *arrayCompSymRef = comp->getSymRefTab()->findOrCreateArrayComponentTypeSymbolRef();
   TR::SymbolReference *classFlagsSymRef = comp->getSymRefTab()->findOrCreateClassFlagsSymbolRef();

   TR::Node *vft = TR::Node::createWithSymRef(node, TR::aloadi, 1, anchoredArrayBaseAddressNode, vftSymRef);
   TR::Node *arrayCompClass = TR::Node::createWithSymRef(node, TR::aloadi, 1, vft, arrayCompSymRef);
   //TR::Node *testIsValueTypeNode = comp()->fej9()->testIsClassValueType(arrayCompClass);
   TR::Node *testIsValueTypeNode = testIsClassValueType(arrayCompClass, comp);

   // The branch destination will be set up later
   TR::Node *ifNode = TR::Node::createif(TR::ificmpne, testIsValueTypeNode, TR::Node::iconst(node, 0));

   // Copy register dependency to the ificmpne node that's being appended to the current block
   copyRegisterDependency(arrayElementStoreBlock->getExit()->getNode(), ifNode);

   // Append the ificmpne node that checks classFlags to the original block
   originalBlock->append(TR::TreeTop::create(comp, ifNode));

   if (enableTrace)
      traceMsg(comp, "Append ifNode n%dn to block_%d\n", ifNode->getGlobalIndex(), originalBlock->getNumber());


   ///////////////////////////////////////
   // 9. Fix the register dependency after ifNode copying

   // Adjust the reference count of the GlRegDeps of the BBExit for arrayElementStoreBlock since it will be replaced by
   // the previously saved tmpGlRegDeps
   if (arrayElementStoreBlock->getExit()->getNode()->getNumChildren() > 0)
      {
      TR::Node *origRegDeps = arrayElementStoreBlock->getExit()->getNode()->getFirstChild();
      prepareToReplaceNode(origRegDeps);
      origRegDeps->decReferenceCount();
      arrayElementStoreBlock->getExit()->getNode()->setNumChildren(0);
      }

   if (tmpGlRegDeps)
      {
      arrayElementStoreBlock->getExit()->getNode()->setNumChildren(1);
      arrayElementStoreBlock->getExit()->getNode()->setAndIncChild(0, tmpGlRegDeps);
      }


   ///////////////////////////////////////
   // 10. Set up the edges between the blocks
   ifNode->setBranchDestination(helperCallBlock->getEntry());

   cfg->addEdge(originalBlock, helperCallBlock);

   cfg->removeEdge(arrayElementStoreBlock, helperCallBlock);
   cfg->addEdge(arrayElementStoreBlock, blockAfterHelperCall);

   // Force nodeIter to first TreeTop of next block so that
   // moving callBlock won't cause problems while iterating
   while (nodeIter.currentTree() != blockAfterHelperCall->getEntry())
       ++nodeIter;

   arrayElementStoreBlock->getExit()->join(blockAfterHelperCall->getEntry());

   TR::TreeTop *lastTreeTop = comp->getMethodSymbol()->getLastTreeTop();
   lastTreeTop->insertTreeTopsAfterMe(helperCallBlock->getEntry(), helperCallBlock->getExit());

   // Add Goto block from helper call to the merge block
   TR::Node *gotoAfterHelperCallNode = TR::Node::create(helperCallBlock->getExit()->getNode(), TR::Goto, 0, blockAfterHelperCall->getEntry());
   helperCallBlock->append(TR::TreeTop::create(comp, gotoAfterHelperCallNode));

   if (helperCallBlock->getExit()->getNode()->getNumChildren() > 0)
      {
      TR::Node *deps = helperCallBlock->getExit()->getNode()->getChild(0);
      helperCallBlock->getExit()->getNode()->setNumChildren(0);
      deps->decReferenceCount();
      gotoAfterHelperCallNode->addChildren(&deps, 1);
      }
   }
