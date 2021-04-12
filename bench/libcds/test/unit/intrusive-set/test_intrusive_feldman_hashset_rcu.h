// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSUNIT_SET_TEST_INTRUSIVE_FELDMAN_HASHSET_RCU_H
#define CDSUNIT_SET_TEST_INTRUSIVE_FELDMAN_HASHSET_RCU_H

#include "test_intrusive_feldman_hashset.h"

#include <cds/intrusive/feldman_hashset_rcu.h>

namespace ci = cds::intrusive;
namespace co = cds::opt;

template <class RCU>
class IntrusiveFeldmanHashSet : public cds_test::intrusive_feldman_hashset
{
    typedef cds_test::intrusive_feldman_hashset base_class;

protected:
    typedef cds::urcu::gc<RCU> rcu_type;

    template <class Set>
    void test( Set& s )
    {
        // Precondition: set is empty
        // Postcondition: set is empty

        base_class::test( s );

        ASSERT_TRUE( s.empty());
        ASSERT_CONTAINER_SIZE( s, 0 );

        typedef typename Set::value_type value_type;
        size_t const nSetSize = std::max( s.head_size() * 2, static_cast<size_t>(100));

        std::vector< value_type > data;
        std::vector< size_t> indices;
        data.reserve( nSetSize );
        indices.reserve( nSetSize );
        for ( size_t key = 0; key < nSetSize; ++key ) {
            data.push_back( value_type( static_cast<int>(key)));
            indices.push_back( key );
        }
        shuffle( indices.begin(), indices.end());

        typename Set::exempt_ptr xp;
        value_type * rp;
        typedef typename Set::rcu_lock rcu_lock;

        // get/extract from empty set
        for ( auto idx : indices ) {
            auto& i = data[idx];

            {
                rcu_lock l;
                rp = s.get( i.key());
                ASSERT_TRUE( !rp );
            }

            xp = s.extract( i.key());
            ASSERT_TRUE( !xp );
        }

        // fill set
        for ( auto& i : data ) {
            i.nDisposeCount = 0;
            ASSERT_TRUE( s.insert( i ));
        }

        // get/extract
        for ( auto idx : indices ) {
            auto& i = data[idx];

            {
                rcu_lock l;
                EXPECT_EQ( i.nFindCount, 0u );
                rp = s.get( i.key());
                ASSERT_FALSE( !rp );
                ++rp->nFindCount;
                EXPECT_EQ( i.nFindCount, 1u );
            }

            EXPECT_EQ( i.nEraseCount, 0u );
            xp = s.extract( i.key());
            ASSERT_FALSE( !xp );
            ++xp->nEraseCount;
            EXPECT_EQ( i.nEraseCount, 1u );

            xp = s.extract( i.key());
            ASSERT_TRUE( !xp );
        }

        ASSERT_TRUE( s.empty());
        ASSERT_CONTAINER_SIZE( s, 0 );

        // Force retiring cycle
        Set::gc::force_dispose();
        for ( auto& i : data ) {
            EXPECT_EQ( i.nDisposeCount, 1u );
        }
    }

    void SetUp()
    {
        RCU::Construct();
        cds::threading::Manager::attachThread();
    }

    void TearDown()
    {
        cds::threading::Manager::detachThread();
        RCU::Destruct();
    }
};

TYPED_TEST_CASE_P( IntrusiveFeldmanHashSet );

TYPED_TEST_P( IntrusiveFeldmanHashSet, compare )
{
    typedef typename TestFixture::rcu_type rcu_type;

    struct traits : public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor hash_accessor;
        typedef typename TestFixture::cmp compare;
        typedef typename TestFixture::mock_disposer disposer;
    };

    typedef ci::FeldmanHashSet< rcu_type, typename TestFixture::int_item, traits > set_type;

    set_type s;
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, less )
{
    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item,
        typename ci::feldman_hashset::make_traits<
            ci::feldman_hashset::hash_accessor< typename TestFixture::hash_accessor >
            , ci::opt::less< std::less<int>>
            , ci::opt::disposer< typename TestFixture::mock_disposer>
        >::type
    > set_type;

    set_type s( 5, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, cmpmix )
{
    struct traits : public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor hash_accessor;
        typedef typename TestFixture::cmp compare;
        typedef std::less<int> less;
        typedef typename TestFixture::mock_disposer disposer;
        typedef typename TestFixture::simple_item_counter item_counter;
    };

    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item, traits > set_type;

    set_type s( 3, 4 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, backoff )
{
    struct traits : public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor hash_accessor;
        typedef typename TestFixture::cmp compare;
        typedef typename TestFixture::mock_disposer disposer;
        typedef cds::backoff::empty back_off;
        typedef ci::opt::v::sequential_consistent memory_model;
    };

    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item, traits > set_type;

    set_type s( 8, 3 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, stat )
{
    struct traits : public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor hash_accessor;
        typedef typename TestFixture::cmp compare;
        typedef typename TestFixture::mock_disposer disposer;
        typedef ci::feldman_hashset::stat<> stat;
    };

    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item, traits > set_type;

    set_type s( 8, 3 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, explicit_hash_size )
{
    struct traits: public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor2 hash_accessor;
        enum: size_t {
            hash_size = sizeof( std::declval<typename TestFixture::key_val>().nKey )
        };
        typedef typename TestFixture::cmp2 compare;
        typedef typename TestFixture::mock_disposer disposer;
        typedef ci::feldman_hashset::stat<> stat;
    };

    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item2, traits > set_type;

    set_type s( 8, 3 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, byte_cut )
{
    struct traits: public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor hash_accessor;
        typedef cds::algo::byte_splitter< int > hash_splitter;
        typedef typename TestFixture::cmp compare;
        typedef typename TestFixture::mock_disposer disposer;
    };

    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item, traits > set_type;

    set_type s( 8, 8 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveFeldmanHashSet, byte_cut_explicit_hash_size )
{
    struct traits: public ci::feldman_hashset::traits
    {
        typedef typename TestFixture::hash_accessor2 hash_accessor;
        typedef cds::algo::byte_splitter< typename TestFixture::key_val > hash_splitter;
        enum: size_t {
            hash_size = sizeof( std::declval<typename TestFixture::key_val>().nKey )
        };
        typedef typename TestFixture::cmp2 compare;
        typedef typename TestFixture::mock_disposer disposer;
        typedef ci::feldman_hashset::stat<> stat;
    };

    typedef ci::FeldmanHashSet< typename TestFixture::rcu_type, typename TestFixture::int_item2, traits > set_type;

    set_type s( 8, 8 );
    this->test( s );
}

// GCC 5: All test names should be written on single line, otherwise a runtime error will be encountered like as
// "No test named <test_name> can be found in this test case"
REGISTER_TYPED_TEST_CASE_P( IntrusiveFeldmanHashSet,
    compare, less, cmpmix, backoff, stat, explicit_hash_size, byte_cut, byte_cut_explicit_hash_size
    );


#endif // #ifndef CDSUNIT_SET_TEST_INTRUSIVE_FELDMAN_HASHSET_RCU_H
