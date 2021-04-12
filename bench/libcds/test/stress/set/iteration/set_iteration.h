// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include "set_type.h"
#include <cds_test/city.h>

namespace set {

// Test for set's thread-safe iterator:
//   Several thread inserts/erases elemets from the set.
//   Dedicated Iterator thread iterates over the set, calculates CityHash for each element
//   and stores it in the element.
// Test goal: no crash

#define TEST_CASE(TAG, X)  void X();

    class Set_Iteration: public cds_test::stress_fixture
    {
    public:
        static size_t s_nSetSize;               // set size
        static size_t s_nInsertThreadCount;     // count of insertion thread
        static size_t s_nDeleteThreadCount;     // count of deletion thread
        static size_t s_nThreadPassCount;       // pass count for each thread
        static size_t s_nMaxLoadFactor;         // maximum load factor

        static size_t s_nCuckooInitialSize;     // initial size for CuckooSet
        static size_t s_nCuckooProbesetSize;    // CuckooSet probeset size (only for list-based probeset)
        static size_t s_nCuckooProbesetThreshold; // CUckooSet probeset threshold (0 - use default)

        static size_t s_nFeldmanSet_HeadBits;
        static size_t s_nFeldmanSet_ArrayBits;

        static size_t s_nLoadFactor;
        static std::vector<std::string>  m_arrString;

        static void SetUpTestCase();
        static void TearDownTestCase();

        void on_modifier_done()
        {
            m_nModifierCount.fetch_sub( 1, atomics::memory_order_relaxed );
        }

        bool all_modifiers_done() const
        {
            return m_nModifierCount.load( atomics::memory_order_relaxed ) == 0;
        }

        typedef std::string key_type;

        struct value_type
        {
            size_t   val;
            uint64_t hash;

            explicit value_type( size_t v )
                : val(v)
                , hash(0)
            {}
        };

    private:
        enum {
            insert_thread,
            delete_thread,
            extract_thread,
            iterator_thread
        };

        atomics::atomic<size_t> m_nModifierCount;

        template <class Set>
        class Inserter: public cds_test::thread
        {
            typedef cds_test::thread base_class;

            Set&     m_Set;
            typedef typename Set::value_type keyval_type;

        public:
            size_t  m_nInsertSuccess = 0;
            size_t  m_nInsertFailed = 0;

        public:
            Inserter( cds_test::thread_pool& pool, Set& set )
                : base_class( pool, insert_thread )
                , m_Set( set )
            {}

            Inserter( Inserter& src )
                : base_class( src )
                , m_Set( src.m_Set )
            {}

            virtual thread * clone()
            {
                return new Inserter( *this );
            }

            virtual void test()
            {
                Set& rSet = m_Set;

                Set_Iteration& fixture = pool().template fixture<Set_Iteration>();
                size_t nArrSize = m_arrString.size();
                size_t const nSetSize = fixture.s_nSetSize;
                size_t const nPassCount = fixture.s_nThreadPassCount;

                if ( id() & 1 ) {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = 0; nItem < nSetSize; ++nItem ) {
                            if ( rSet.insert( keyval_type( m_arrString[nItem % nArrSize], nItem * 8 )))
                                ++m_nInsertSuccess;
                            else
                                ++m_nInsertFailed;
                        }
                    }
                }
                else {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = nSetSize; nItem > 0; --nItem ) {
                            if ( rSet.insert( keyval_type( m_arrString[nItem % nArrSize], nItem * 8 )))
                                ++m_nInsertSuccess;
                            else
                                ++m_nInsertFailed;
                        }
                    }
                }

                fixture.on_modifier_done();
            }
        };

        template <class Set>
        class Deleter: public cds_test::thread
        {
            typedef cds_test::thread base_class;

            Set&     m_Set;
        public:
            size_t  m_nDeleteSuccess = 0;
            size_t  m_nDeleteFailed = 0;

        public:
            Deleter( cds_test::thread_pool& pool, Set& set )
                : base_class( pool, delete_thread )
                , m_Set( set )
            {}

            Deleter( Deleter& src )
                : base_class( src )
                , m_Set( src.m_Set )
            {}

            virtual thread * clone()
            {
                return new Deleter( *this );
            }

            virtual void test()
            {
                Set& rSet = m_Set;

                Set_Iteration& fixture = pool().template fixture<Set_Iteration>();
                size_t nArrSize = m_arrString.size();
                size_t const nSetSize = fixture.s_nSetSize;
                size_t const nPassCount = fixture.s_nThreadPassCount;

                if ( id() & 1 ) {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = 0; nItem < nSetSize; ++nItem ) {
                            if ( rSet.erase( m_arrString[nItem % nArrSize] ))
                                ++m_nDeleteSuccess;
                            else
                                ++m_nDeleteFailed;
                        }
                    }
                }
                else {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = nSetSize; nItem > 0; --nItem ) {
                            if ( rSet.erase( m_arrString[nItem % nArrSize] ))
                                ++m_nDeleteSuccess;
                            else
                                ++m_nDeleteFailed;
                        }
                    }
                }

                fixture.on_modifier_done();
            }
        };

        template <typename GC, class Set>
        class Extractor: public cds_test::thread
        {
            typedef cds_test::thread base_class;
            Set&     m_Set;

        public:
            size_t  m_nDeleteSuccess = 0;
            size_t  m_nDeleteFailed = 0;

        public:
            Extractor( cds_test::thread_pool& pool, Set& set )
                : base_class( pool, extract_thread )
                , m_Set( set )
            {}

            Extractor( Extractor& src )
                : base_class( src )
                , m_Set( src.m_Set )
            {}

            virtual thread * clone()
            {
                return new Extractor( *this );
            }

            virtual void test()
            {
                Set& rSet = m_Set;

                typename Set::guarded_ptr gp;

                Set_Iteration& fixture = pool().template fixture<Set_Iteration>();
                size_t nArrSize = m_arrString.size();
                size_t const nSetSize = fixture.s_nSetSize;
                size_t const nPassCount = fixture.s_nThreadPassCount;

                if ( id() & 1 ) {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = 0; nItem < nSetSize; ++nItem ) {
                            gp = rSet.extract( m_arrString[nItem % nArrSize] );
                            if ( gp )
                                ++m_nDeleteSuccess;
                            else
                                ++m_nDeleteFailed;
                            gp.release();
                        }
                    }
                }
                else {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = nSetSize; nItem > 0; --nItem ) {
                            gp = rSet.extract( m_arrString[nItem % nArrSize] );
                            if ( gp )
                                ++m_nDeleteSuccess;
                            else
                                ++m_nDeleteFailed;
                            gp.release();
                        }
                    }
                }

                fixture.on_modifier_done();
            }
        };

        template <typename RCU, class Set>
        class Extractor<cds::urcu::gc<RCU>, Set >: public cds_test::thread
        {
            typedef cds_test::thread base_class;
            Set&     m_Set;

        public:
            size_t  m_nDeleteSuccess = 0;
            size_t  m_nDeleteFailed = 0;

        public:
            Extractor( cds_test::thread_pool& pool, Set& set )
                : base_class( pool, extract_thread )
                , m_Set( set )
            {}

            Extractor( Extractor& src )
                : base_class( src )
                , m_Set( src.m_Set )
            {}

            virtual thread * clone()
            {
                return new Extractor( *this );
            }

            virtual void test()
            {
                Set& rSet = m_Set;

                typename Set::exempt_ptr xp;

                Set_Iteration& fixture = pool().template fixture<Set_Iteration>();
                size_t nArrSize = m_arrString.size();
                size_t const nSetSize = fixture.s_nSetSize;
                size_t const nPassCount = fixture.s_nThreadPassCount;

                if ( id() & 1 ) {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = 0; nItem < nSetSize; ++nItem ) {
                            if ( Set::c_bExtractLockExternal ) {
                                typename Set::rcu_lock l;
                                xp = rSet.extract( m_arrString[nItem % nArrSize] );
                                if ( xp )
                                    ++m_nDeleteSuccess;
                                else
                                    ++m_nDeleteFailed;
                            }
                            else {
                                xp = rSet.extract( m_arrString[nItem % nArrSize] );
                                if ( xp )
                                    ++m_nDeleteSuccess;
                                else
                                    ++m_nDeleteFailed;
                            }
                            xp.release();
                        }
                    }
                }
                else {
                    for ( size_t nPass = 0; nPass < nPassCount; ++nPass ) {
                        for ( size_t nItem = nSetSize; nItem > 0; --nItem ) {
                            if ( Set::c_bExtractLockExternal ) {
                                typename Set::rcu_lock l;
                                xp = rSet.extract( m_arrString[nItem % nArrSize] );
                                if ( xp )
                                    ++m_nDeleteSuccess;
                                else
                                    ++m_nDeleteFailed;
                            }
                            else {
                                xp = rSet.extract( m_arrString[nItem % nArrSize] );
                                if ( xp )
                                    ++m_nDeleteSuccess;
                                else
                                    ++m_nDeleteFailed;
                            }
                            xp.release();
                        }
                    }
                }

                fixture.on_modifier_done();
            }
        };

        template <typename GC, class Set>
        class Iterator: public cds_test::thread
        {
            typedef cds_test::thread base_class;

            Set&     m_Set;
            typedef typename Set::value_type keyval_type;

        public:
            size_t  m_nPassCount = 0;
            size_t  m_nVisitCount = 0; // how many items the iterator visited

        public:
            Iterator( cds_test::thread_pool& pool, Set& set )
                : base_class( pool, iterator_thread )
                , m_Set( set )
            {}

            Iterator( Iterator& src )
                : base_class( src )
                , m_Set( src.m_Set )
            {}

            virtual thread * clone()
            {
                return new Iterator( *this );
            }

            virtual void test()
            {
                Set& rSet = m_Set;

                Set_Iteration& fixture = pool().template fixture<Set_Iteration>();
                while ( !fixture.all_modifiers_done()) {
                    ++m_nPassCount;
                    typename Set::iterator it;
                    typename Set::iterator itEnd;
                    itEnd = rSet.end();
                    for ( it = rSet.begin(); it != itEnd; ++it ) {
#if CDS_BUILD_BITS == 64
                        it->val.hash = CityHash64( it->key.c_str(), it->key.length());
#else
                        it->val.hash = std::hash<std::string>()( it->key );
#endif
                        ++m_nVisitCount;
                    }
                }
            }
        };

        template <typename RCU, class Set>
        class Iterator<cds::urcu::gc<RCU>, Set>: public cds_test::thread
        {
            typedef cds_test::thread base_class;

            Set&     m_Set;
            typedef typename Set::value_type keyval_type;

        public:
            size_t  m_nPassCount = 0;
            size_t  m_nVisitCount = 0; // how many items the iterator visited

        public:
            Iterator( cds_test::thread_pool& pool, Set& set )
                : base_class( pool, iterator_thread )
                , m_Set( set )
            {}

            Iterator( Iterator& src )
                : base_class( src )
                , m_Set( src.m_Set )
            {}

            virtual thread * clone()
            {
                return new Iterator( *this );
            }

            virtual void test()
            {
                Set& rSet = m_Set;

                Set_Iteration& fixture = pool().template fixture<Set_Iteration>();
                while ( !fixture.all_modifiers_done()) {
                    ++m_nPassCount;
                    typename Set::rcu_lock l;
                    for ( auto it = rSet.begin(); it != rSet.end(); ++it ) {
#if CDS_BUILD_BITS == 64
                        it->val.hash = CityHash64( it->key.c_str(), it->key.length());
#else
                        it->val.hash = std::hash<std::string>()(it->key);
#endif
                        ++m_nVisitCount;
                    }
                }
            }
        };

    protected:
        template <class Set>
        void do_test( Set& testSet )
        {
            typedef Inserter<Set> InserterThread;
            typedef Deleter<Set>  DeleterThread;
            typedef Iterator<typename Set::gc, Set> IteratorThread;

            cds_test::thread_pool& pool = get_pool();
            pool.add( new InserterThread( pool, testSet ), s_nInsertThreadCount );
            pool.add( new DeleterThread( pool, testSet ), s_nDeleteThreadCount );

            m_nModifierCount.store( pool.size(), atomics::memory_order_relaxed );
            pool.add( new IteratorThread( pool, testSet ), 1 );

            propout() << std::make_pair( "insert_thread_count", s_nInsertThreadCount )
                << std::make_pair( "delete_thread_count", s_nDeleteThreadCount )
                << std::make_pair( "thread_pass_count", s_nThreadPassCount )
                << std::make_pair( "set_size", s_nSetSize );

            std::chrono::milliseconds duration = pool.run();

            propout() << std::make_pair( "duration", duration );

            size_t nInsertSuccess = 0;
            size_t nInsertFailed = 0;
            size_t nDeleteSuccess = 0;
            size_t nDeleteFailed = 0;
            size_t nIteratorPassCount = 0;
            size_t nIteratorVisitCount = 0;
            for ( size_t i = 0; i < pool.size(); ++i ) {
                cds_test::thread& thr = pool.get( i );
                switch ( thr.type()) {
                case insert_thread:
                    {
                        InserterThread& inserter = static_cast<InserterThread&>( thr );
                        nInsertSuccess += inserter.m_nInsertSuccess;
                        nInsertFailed += inserter.m_nInsertFailed;
                    }
                    break;
                case delete_thread:
                    {
                        DeleterThread& deleter = static_cast<DeleterThread&>(thr);
                        nDeleteSuccess += deleter.m_nDeleteSuccess;
                        nDeleteFailed += deleter.m_nDeleteFailed;
                    }
                    break;
                case iterator_thread:
                    {
                        IteratorThread& iter = static_cast<IteratorThread&>(thr);
                        nIteratorPassCount += iter.m_nPassCount;
                        nIteratorVisitCount += iter.m_nVisitCount;
                    }
                    break;
                default:
                    assert( false ); // Forgot anything?..
                }
            }

            propout()
                << std::make_pair( "insert_success", nInsertSuccess )
                << std::make_pair( "delete_success", nDeleteSuccess )
                << std::make_pair( "insert_failed", nInsertFailed )
                << std::make_pair( "delete_failed", nDeleteFailed )
                << std::make_pair( "iterator_pass_count", nIteratorPassCount )
                << std::make_pair( "iterator_visit_count", nIteratorVisitCount )
                << std::make_pair( "final_set_size", testSet.size());

            testSet.clear();
            EXPECT_TRUE( testSet.empty());

            additional_check( testSet );
            print_stat( propout(), testSet );
            additional_cleanup( testSet );
        }

        template <class Set>
        void do_test_extract( Set& testSet )
        {
            typedef Inserter<Set> InserterThread;
            typedef Deleter<Set>  DeleterThread;
            typedef Extractor<typename Set::gc, Set> ExtractThread;
            typedef Iterator<typename Set::gc, Set> IteratorThread;

            size_t const nDelThreadCount = s_nDeleteThreadCount / 2;
            size_t const nExtractThreadCount = s_nDeleteThreadCount - nDelThreadCount;

            cds_test::thread_pool& pool = get_pool();
            pool.add( new InserterThread( pool, testSet ), s_nInsertThreadCount );
            pool.add( new DeleterThread( pool, testSet ), nDelThreadCount );
            pool.add( new ExtractThread( pool, testSet ), nExtractThreadCount );

            m_nModifierCount.store( pool.size(), atomics::memory_order_relaxed );
            pool.add( new IteratorThread( pool, testSet ), 1 );

            propout() << std::make_pair( "insert_thread_count", s_nInsertThreadCount )
                << std::make_pair( "delete_thread_count", nDelThreadCount )
                << std::make_pair( "extract_thread_count", nExtractThreadCount )
                << std::make_pair( "thread_pass_count", s_nThreadPassCount )
                << std::make_pair( "set_size", s_nSetSize );

            std::chrono::milliseconds duration = pool.run();

            propout() << std::make_pair( "duration", duration );

            size_t nInsertSuccess = 0;
            size_t nInsertFailed = 0;
            size_t nDeleteSuccess = 0;
            size_t nDeleteFailed = 0;
            size_t nExtractSuccess = 0;
            size_t nExtractFailed = 0;
            size_t nIteratorPassCount = 0;
            size_t nIteratorVisitCount = 0;
            for ( size_t i = 0; i < pool.size(); ++i ) {
                cds_test::thread& thr = pool.get( i );
                switch ( thr.type()) {
                case insert_thread:
                    {
                        InserterThread& inserter = static_cast<InserterThread&>(thr);
                        nInsertSuccess += inserter.m_nInsertSuccess;
                        nInsertFailed += inserter.m_nInsertFailed;
                    }
                    break;
                case delete_thread:
                    {
                        DeleterThread& deleter = static_cast<DeleterThread&>(thr);
                        nDeleteSuccess += deleter.m_nDeleteSuccess;
                        nDeleteFailed += deleter.m_nDeleteFailed;
                    }
                    break;
                case extract_thread:
                    {
                        ExtractThread& extractor = static_cast<ExtractThread&>(thr);
                        nExtractSuccess += extractor.m_nDeleteSuccess;
                        nExtractFailed += extractor.m_nDeleteFailed;
                    }
                    break;
                case iterator_thread:
                    {
                        IteratorThread& iter = static_cast<IteratorThread&>(thr);
                        nIteratorPassCount += iter.m_nPassCount;
                        nIteratorVisitCount += iter.m_nVisitCount;
                    }
                    break;
                default:
                    assert( false ); // Forgot anything?..
                }
            }

            propout()
                << std::make_pair( "insert_success", nInsertSuccess )
                << std::make_pair( "delete_success", nDeleteSuccess )
                << std::make_pair( "extract_success", nExtractSuccess )
                << std::make_pair( "insert_failed",  nInsertFailed )
                << std::make_pair( "delete_failed",  nDeleteFailed )
                << std::make_pair( "extract_failed", nExtractFailed )
                << std::make_pair( "iterator_pass_count", nIteratorPassCount )
                << std::make_pair( "iterator_visit_count", nIteratorVisitCount )
                << std::make_pair( "final_set_size", testSet.size());

            testSet.clear();
            EXPECT_TRUE( testSet.empty());

            additional_check( testSet );
            print_stat( propout(), testSet );
            additional_cleanup( testSet );
        }

        template <class Set>
        void run_test()
        {
            ASSERT_TRUE( m_arrString.size() > 0 );

            Set s( *this );
            do_test( s );
        }

        template <class Set>
        void run_test_extract()
        {
            ASSERT_TRUE( m_arrString.size() > 0 );

            Set s( *this );
            do_test_extract( s );
        }
    };

    class Set_Iteration_LF: public Set_Iteration
        , public ::testing::WithParamInterface<size_t>
    {
    public:
        template <class Set>
        void run_test()
        {
            s_nLoadFactor = GetParam();
            propout() << std::make_pair( "load_factor", s_nLoadFactor );
            Set_Iteration::run_test<Set>();
        }

        template <class Set>
        void run_test_extract()
        {
            s_nLoadFactor = GetParam();
            propout() << std::make_pair( "load_factor", s_nLoadFactor );
            Set_Iteration::run_test_extract<Set>();
        }

        static std::vector<size_t> get_load_factors();
    };

} // namespace set
