// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)
#ifndef CDSUNIT_SET_TEST_INTRUSIVE_MICHAEL_LAZY_RCU_H
#define CDSUNIT_SET_TEST_INTRUSIVE_MICHAEL_LAZY_RCU_H

#include "test_intrusive_set_rcu.h"
#include <cds/intrusive/lazy_list_rcu.h>
#include <cds/intrusive/michael_set_rcu.h>

namespace ci = cds::intrusive;

template <class RCU>
class IntrusiveMichaelLazySet: public cds_test::intrusive_set_rcu
{
    typedef cds_test::intrusive_set_rcu base_class;
public:
    typedef cds::urcu::gc<RCU> rcu_type;
    typedef typename base_class::base_int_item< ci::lazy_list::node<rcu_type>>   base_item_type;
    typedef typename base_class::base_int_item< ci::lazy_list::node<rcu_type, std::mutex>>   base_mutex_item_type;
    typedef typename base_class::member_int_item< ci::lazy_list::node<rcu_type>> member_item_type;
    typedef typename base_class::member_int_item< ci::lazy_list::node<rcu_type, std::mutex>> member_mutex_item_type;

protected:
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

TYPED_TEST_CASE_P( IntrusiveMichaelLazySet );

TYPED_TEST_P( IntrusiveMichaelLazySet, base_cmp )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::base_item_type base_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::template cmp<base_item_type> item_cmp;
    typedef typename TestFixture::hash_int hash_int;

    typedef ci::LazyList< rcu_type
        , base_item_type
        , typename ci::lazy_list::make_traits<
            ci::opt::hook< ci::lazy_list::base_hook< ci::opt::gc< rcu_type > > >
            , ci::opt::compare< item_cmp >
            , ci::opt::disposer< mock_disposer >
        >::type
    > bucket_type;

    typedef ci::MichaelHashSet< rcu_type, bucket_type,
        typename ci::michael_set::make_traits<
            ci::opt::hash< hash_int >
        >::type
    > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, base_less )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::base_item_type base_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::template less<base_item_type> item_less;
    typedef typename TestFixture::hash_int hash_int;

    typedef ci::LazyList< rcu_type
        , base_item_type
        , typename ci::lazy_list::make_traits<
            ci::opt::hook< ci::lazy_list::base_hook< ci::opt::gc< rcu_type >>>
            , ci::opt::less< item_less >
            , ci::opt::disposer< mock_disposer >
        >::type
    > bucket_type;

    typedef ci::MichaelHashSet< rcu_type, bucket_type,
        typename ci::michael_set::make_traits<
            ci::opt::hash< hash_int >
        >::type
    > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, base_cmpmix )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::base_item_type base_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits : public ci::lazy_list::traits
    {
        typedef ci::lazy_list::base_hook< ci::opt::gc<rcu_type>> hook;
        typedef typename TestFixture::template less<base_item_type> less;
        typedef typename TestFixture::template cmp<base_item_type> compare;
        typedef mock_disposer disposer;
    };
    typedef ci::LazyList< rcu_type, base_item_type, list_traits > bucket_type;

    struct set_traits : public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, base_mutex )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::base_mutex_item_type base_mutex_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits : public ci::lazy_list::traits
    {
        typedef ci::lazy_list::base_hook< ci::opt::gc<rcu_type>, ci::opt::lock_type<std::mutex>> hook;
        typedef typename TestFixture::template less<base_mutex_item_type> less;
        typedef typename TestFixture::template cmp<base_mutex_item_type> compare;
        typedef mock_disposer disposer;
    };
    typedef ci::LazyList< rcu_type, base_mutex_item_type, list_traits > bucket_type;

    struct set_traits : public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, base_stat )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::base_item_type base_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits: public ci::lazy_list::traits
    {
        typedef ci::lazy_list::base_hook< ci::opt::gc<rcu_type>> hook;
        typedef typename TestFixture::template less<base_item_type> less;
        typedef mock_disposer disposer;
        typedef ci::lazy_list::stat<> stat;
    };
    typedef ci::LazyList< rcu_type, base_item_type, list_traits > bucket_type;

    struct set_traits: public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
    EXPECT_GE( s.statistics().m_nInsertSuccess, 0u );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, base_wrapped_stat )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::base_item_type base_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits: public ci::lazy_list::traits
    {
        typedef ci::lazy_list::base_hook< ci::opt::gc<rcu_type>> hook;
        typedef typename TestFixture::template less<base_item_type> less;
        typedef mock_disposer disposer;
        typedef ci::lazy_list::wrapped_stat<> stat;
    };
    typedef ci::LazyList< rcu_type, base_item_type, list_traits > bucket_type;

    struct set_traits: public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
    EXPECT_GE( s.statistics().m_nInsertSuccess, 0u );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, member_cmp )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::member_item_type member_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::template cmp<member_item_type> item_cmp;
    typedef typename TestFixture::hash_int hash_int;

    typedef ci::LazyList< rcu_type
        , member_item_type
        , typename ci::lazy_list::make_traits<
            ci::opt::hook< ci::lazy_list::member_hook<
                offsetof( member_item_type, hMember ),
                ci::opt::gc<rcu_type>
            >>
            , ci::opt::compare< item_cmp >
            , ci::opt::disposer< mock_disposer >
        >::type
    >    bucket_type;

    typedef ci::MichaelHashSet< rcu_type, bucket_type,
        typename ci::michael_set::make_traits<
            ci::opt::hash< hash_int >
        >::type
    > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, member_less )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::member_item_type member_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::template less<member_item_type> item_less;
    typedef typename TestFixture::hash_int hash_int;

    typedef ci::LazyList< rcu_type
        , member_item_type
        , typename ci::lazy_list::make_traits<
            ci::opt::hook< ci::lazy_list::member_hook<
                offsetof( member_item_type, hMember ),
                ci::opt::gc<rcu_type>
            > >
            , ci::opt::less< item_less >
            , ci::opt::disposer< mock_disposer >
        >::type
    > bucket_type;

    typedef ci::MichaelHashSet< rcu_type, bucket_type,
        typename ci::michael_set::make_traits<
            ci::opt::hash< hash_int >
        >::type
    > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, member_cmpmix )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::member_item_type member_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits : public ci::lazy_list::traits
    {
        typedef ci::lazy_list::member_hook< offsetof( member_item_type, hMember ), ci::opt::gc<rcu_type>> hook;
        typedef typename TestFixture::template less<member_item_type> less;
        typedef typename TestFixture::template cmp<member_item_type> compare;
        typedef mock_disposer disposer;
    };
    typedef ci::LazyList< rcu_type, member_item_type, list_traits > bucket_type;

    struct set_traits : public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, member_mutex )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::member_mutex_item_type member_mutex_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits : public ci::lazy_list::traits
    {
        typedef ci::lazy_list::member_hook< offsetof( member_mutex_item_type, hMember ), ci::opt::gc<rcu_type>, ci::opt::lock_type<std::mutex>> hook;
        typedef typename TestFixture::template less<member_mutex_item_type> less;
        typedef typename TestFixture::template cmp<member_mutex_item_type> compare;
        typedef mock_disposer disposer;
    };
    typedef ci::LazyList< rcu_type, member_mutex_item_type, list_traits > bucket_type;

    struct set_traits : public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, member_stat )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::member_item_type member_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits: public ci::lazy_list::traits
    {
        typedef ci::lazy_list::member_hook< offsetof( member_item_type, hMember ), ci::opt::gc<rcu_type>> hook;
        typedef typename TestFixture::template cmp<member_item_type> compare;
        typedef mock_disposer disposer;
        typedef ci::lazy_list::stat<> stat;
    };
    typedef ci::LazyList< rcu_type, member_item_type, list_traits > bucket_type;

    struct set_traits: public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
    EXPECT_GE( s.statistics().m_nInsertSuccess, 0u );
}

TYPED_TEST_P( IntrusiveMichaelLazySet, member_wrapped_stat )
{
    typedef typename TestFixture::rcu_type rcu_type;
    typedef typename TestFixture::member_item_type member_item_type;
    typedef typename TestFixture::mock_disposer mock_disposer;
    typedef typename TestFixture::hash_int hash_int;

    struct list_traits: public ci::lazy_list::traits
    {
        typedef ci::lazy_list::member_hook< offsetof( member_item_type, hMember ), ci::opt::gc<rcu_type>> hook;
        typedef typename TestFixture::template cmp<member_item_type> compare;
        typedef mock_disposer disposer;
        typedef ci::lazy_list::wrapped_stat<> stat;
    };
    typedef ci::LazyList< rcu_type, member_item_type, list_traits > bucket_type;

    struct set_traits: public ci::michael_set::traits
    {
        typedef hash_int hash;
        typedef typename TestFixture::simple_item_counter item_counter;
    };
    typedef ci::MichaelHashSet< rcu_type, bucket_type, set_traits > set_type;

    set_type s( TestFixture::kSize, 2 );
    this->test( s );
    EXPECT_GE( s.statistics().m_nInsertSuccess, 0u );
}

// GCC 5: All test names should be written on single line, otherwise a runtime error will be encountered like as
// "No test named <test_name> can be found in this test case"
REGISTER_TYPED_TEST_CASE_P( IntrusiveMichaelLazySet,
    base_cmp, base_less, base_cmpmix, base_mutex, base_stat, base_wrapped_stat, member_cmp, member_less, member_cmpmix, member_mutex, member_stat, member_wrapped_stat
);


#endif // CDSUNIT_SET_TEST_INTRUSIVE_MICHAEL_LAZY_RCU_H

