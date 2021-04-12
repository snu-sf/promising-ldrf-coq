// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include "test_data.h"
#include <cds/intrusive/mspriority_queue.h>

namespace {

    struct disposer {
        size_t   m_nCallCount;

        disposer()
            : m_nCallCount( 0 )
        {}

        template <typename T>
        void operator()( T& )
        {
            ++m_nCallCount;
        }
    };

    class IntrusiveMSPQueue : public cds_test::PQueueTest
    {
        typedef cds_test::PQueueTest base_class;
    protected:
        template <class PQueue>
        void test( PQueue& pq )
        {
            data_array<value_type> arr( pq.capacity());
            value_type * pFirst = arr.begin();
            value_type * pLast = arr.end();

            ASSERT_TRUE( pq.empty());
            ASSERT_FALSE( pq.full());
            ASSERT_EQ( pq.size(), 0u );
            ASSERT_EQ( pq.capacity(), static_cast<size_t>( base_class::c_nCapacity - 1 ));

            size_t nSize = 0;

            // Push test
            for ( value_type * p = pFirst; p < pLast; ++p ) {
                ASSERT_TRUE( pq.push( *p ));
                ASSERT_FALSE( pq.empty());
                ASSERT_EQ( pq.size(), ++nSize );
            }

            ASSERT_TRUE( pq.full());
            ASSERT_EQ( pq.size(), pq.capacity());

            // The queue is full
            {
                value_type k( base_class::c_nMinValue + key_type( base_class::c_nCapacity ));
                ASSERT_FALSE( pq.push( k ));
                ASSERT_TRUE( pq.full());
                ASSERT_EQ( pq.size(), pq.capacity());
            }

            // Pop test
            key_type nPrev = base_class::c_nMinValue + key_type( pq.capacity()) - 1;
            value_type * p = pq.pop();
            ASSERT_TRUE( p != nullptr );
            EXPECT_EQ( p->k, nPrev );

            ASSERT_EQ( pq.size(), pq.capacity() - 1 );
            ASSERT_FALSE( pq.full());
            ASSERT_FALSE( pq.empty());

            nSize = pq.size();
            while ( pq.size() > 1u ) {
                p = pq.pop();
                ASSERT_TRUE( p != nullptr );
                EXPECT_EQ( p->k, nPrev - 1 );
                nPrev = p->k;
                --nSize;
                ASSERT_EQ( pq.size(), nSize );
            }

            ASSERT_FALSE( pq.full());
            ASSERT_FALSE( pq.empty());
            ASSERT_EQ( pq.size(), 1u );

            p = pq.pop();
            ASSERT_TRUE( p != nullptr );
            EXPECT_EQ( p->k, base_class::c_nMinValue );

            ASSERT_FALSE( pq.full());
            ASSERT_TRUE( pq.empty());
            ASSERT_EQ( pq.size(), 0u );

            // Clear test
            for ( p = pFirst; p < pLast; ++p ) {
                ASSERT_TRUE( pq.push( *p ));
            }
            EXPECT_FALSE( pq.empty());
            EXPECT_TRUE( pq.full());
            EXPECT_EQ( pq.size(), pq.capacity());
            pq.clear();
            EXPECT_TRUE( pq.empty());
            EXPECT_FALSE( pq.full());
            EXPECT_EQ( pq.size(), 0u );

            // clear_with test
            for ( p = pFirst; p < pLast; ++p ) {
                ASSERT_TRUE( pq.push( *p ));
            }
            ASSERT_FALSE( pq.empty());
            ASSERT_TRUE( pq.full());
            ASSERT_EQ( pq.size(), pq.capacity());

            {
                disposer disp;
                pq.clear_with( std::ref( disp ));
                ASSERT_TRUE( pq.empty());
                ASSERT_FALSE( pq.full());
                ASSERT_EQ( pq.size(), 0u );
                ASSERT_EQ( disp.m_nCallCount, pq.capacity());
            }
        }
    };

    typedef cds::opt::v::initialized_dynamic_buffer< char > dyn_buffer_type;
    typedef cds::opt::v::initialized_static_buffer< char, IntrusiveMSPQueue::c_nCapacity > static_buffer_type;

    TEST_F( IntrusiveMSPQueue, dynamic )
    {
        struct traits : public cds::intrusive::mspriority_queue::traits
        {
            typedef dyn_buffer_type buffer;
        };
        typedef cds::intrusive::MSPriorityQueue< value_type, traits > pqueue;

        pqueue pq( c_nCapacity );
        test( pq );
    }

    TEST_F( IntrusiveMSPQueue, dynamic_cmp )
    {
        struct traits : public cds::intrusive::mspriority_queue::traits
        {
            typedef dyn_buffer_type buffer;
            typedef IntrusiveMSPQueue::compare compare;
        };
        typedef cds::intrusive::MSPriorityQueue< value_type, traits > pqueue;

        pqueue pq( c_nCapacity );
        test( pq );
    }

    TEST_F( IntrusiveMSPQueue, dynamic_less )
    {
        typedef cds::intrusive::MSPriorityQueue< value_type,
            cds::intrusive::mspriority_queue::make_traits<
                cds::opt::buffer< dyn_buffer_type >
                ,cds::opt::less< std::less<value_type> >
            >::type
        > pqueue;

        pqueue pq( c_nCapacity );
        test( pq );
    }

    TEST_F( IntrusiveMSPQueue, dynamic_cmp_less )
    {
        typedef cds::intrusive::MSPriorityQueue< value_type,
            cds::intrusive::mspriority_queue::make_traits<
                cds::opt::buffer< dyn_buffer_type >
                ,cds::opt::less< std::less<value_type> >
                ,cds::opt::compare< IntrusiveMSPQueue::compare >
            >::type
        > pqueue;

        pqueue pq( c_nCapacity );
        test( pq );
    }

    TEST_F( IntrusiveMSPQueue, dynamic_mutex )
    {
        struct traits : public cds::intrusive::mspriority_queue::traits
        {
            typedef dyn_buffer_type buffer;
            typedef IntrusiveMSPQueue::compare compare;
            typedef std::mutex lock_type;
        };
        typedef cds::intrusive::MSPriorityQueue< value_type, traits > pqueue;

        pqueue pq( c_nCapacity );
        test( pq );
    }

    TEST_F( IntrusiveMSPQueue, stat )
    {
        struct traits : public cds::intrusive::mspriority_queue::traits
        {
            typedef static_buffer_type buffer;
        };
        typedef cds::intrusive::MSPriorityQueue< value_type, traits > pqueue;

        std::unique_ptr<pqueue> pq( new pqueue(0));
        test( *pq );
    }

    TEST_F( IntrusiveMSPQueue, stat_cmp )
    {
        typedef cds::intrusive::MSPriorityQueue< value_type,
            cds::intrusive::mspriority_queue::make_traits<
                cds::opt::buffer< static_buffer_type >
                ,cds::opt::compare< compare >
            >::type
        > pqueue;

        std::unique_ptr<pqueue> pq( new pqueue( 0 ));
        test( *pq );
    }

    TEST_F( IntrusiveMSPQueue, stat_less )
    {
        typedef cds::intrusive::MSPriorityQueue< value_type,
            cds::intrusive::mspriority_queue::make_traits<
                cds::opt::buffer< static_buffer_type >
                ,cds::opt::less< less >
            >::type
        > pqueue;

        std::unique_ptr<pqueue> pq( new pqueue( 0 ));
        test( *pq );
    }

    TEST_F( IntrusiveMSPQueue, stat_mutex )
    {
        struct traits : public cds::intrusive::mspriority_queue::traits
        {
            typedef static_buffer_type buffer;
            typedef IntrusiveMSPQueue::compare compare;
            typedef std::mutex lock_type;
        };
        typedef cds::intrusive::MSPriorityQueue< value_type, traits > pqueue;

        std::unique_ptr<pqueue> pq( new pqueue( 0 ));
        test( *pq );
    }

} // namespace
