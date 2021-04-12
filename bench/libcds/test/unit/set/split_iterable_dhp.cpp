// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include "test_split_iterable_hp.h"

#include <cds/container/iterable_list_dhp.h>
#include <cds/container/split_list_set.h>
#include <cds/intrusive/free_list.h>

namespace {
    namespace cc = cds::container;
    typedef cds::gc::DHP gc_type;

    class SplitListIterableSet_DHP : public cds_test::split_iterable_set_hp
    {
    protected:
        typedef cds_test::split_iterable_set_hp base_class;

        void SetUp()
        {
            struct set_traits: public cc::split_list::traits {
                typedef cc::iterable_list_tag ordered_list;
                typedef hash_int hash;
                struct ordered_list_traits: public cc::iterable_list::traits
                {
                    typedef cmp compare;
                };
            };
            typedef cc::SplitListSet< gc_type, int_item, set_traits >   set_type;

            cds::gc::dhp::smr::construct( set_type::c_nHazardPtrCount );
            cds::threading::Manager::attachThread();
        }

        void TearDown()
        {
            cds::threading::Manager::detachThread();
            cds::gc::dhp::smr::destruct();
        }
    };

    TEST_F( SplitListIterableSet_DHP, compare )
    {
        typedef cc::SplitListSet< gc_type, int_item,
            typename cc::split_list::make_traits<
                cc::split_list::ordered_list< cc::iterable_list_tag >
                , cds::opt::hash< hash_int >
                , cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        cds::opt::compare< cmp >
                    >::type
                >
            >::type
        > set_type;

        set_type s( kSize, 2 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, less )
    {
        typedef cc::SplitListSet< gc_type, int_item,
            typename cc::split_list::make_traits<
                cc::split_list::ordered_list< cc::iterable_list_tag >
                , cds::opt::hash< hash_int >
                , cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        cds::opt::less< less >
                    >::type
                >
            >::type
        > set_type;

        set_type s( kSize, 2 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, cmpmix )
    {
        typedef cc::SplitListSet< gc_type, int_item,
            typename cc::split_list::make_traits<
                cc::split_list::ordered_list< cc::iterable_list_tag >
                , cds::opt::hash< hash_int >
                , cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        cds::opt::less< less >
                        , cds::opt::compare< cmp >
                    >::type
                >
            >::type
        > set_type;

        set_type s( kSize, 2 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, item_counting )
    {
        struct set_traits: public cc::split_list::traits
        {
            typedef cc::iterable_list_tag ordered_list;
            typedef hash_int hash;
            typedef cds::atomicity::item_counter item_counter;

            struct ordered_list_traits: public cc::iterable_list::traits
            {
                typedef cmp compare;
                typedef base_class::less less;
                typedef cds::backoff::empty back_off;
            };
        };
        typedef cc::SplitListSet< gc_type, int_item, set_traits > set_type;

        set_type s( kSize, 4 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, stat )
    {
        struct set_traits: public cc::split_list::traits
        {
            typedef cc::iterable_list_tag ordered_list;
            typedef hash_int hash;
            typedef cds::atomicity::item_counter item_counter;
            typedef cc::split_list::stat<> stat;

            struct ordered_list_traits: public cc::iterable_list::traits
            {
                typedef base_class::less less;
                typedef cds::opt::v::sequential_consistent memory_model;
            };
        };
        typedef cc::SplitListSet< gc_type, int_item, set_traits > set_type;

        set_type s( kSize, 2 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, back_off )
    {
        struct set_traits: public cc::split_list::traits
        {
            typedef cc::iterable_list_tag ordered_list;
            typedef hash_int hash;
            typedef cds::atomicity::item_counter item_counter;
            typedef cds::backoff::yield back_off;
            typedef cds::opt::v::sequential_consistent memory_model;

            struct ordered_list_traits: public cc::iterable_list::traits
            {
                typedef cmp compare;
                typedef cds::backoff::pause back_off;
            };
        };
        typedef cc::SplitListSet< gc_type, int_item, set_traits > set_type;

        set_type s( kSize, 3 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, free_list )
    {
        struct set_traits: public cc::split_list::traits
        {
            typedef cc::iterable_list_tag ordered_list;
            typedef hash_int hash;
            typedef cds::atomicity::item_counter item_counter;
            typedef cds::intrusive::FreeList free_list;

            struct ordered_list_traits: public cc::iterable_list::traits
            {
                typedef cmp compare;
                typedef cds::backoff::pause back_off;
            };
        };
        typedef cc::SplitListSet< gc_type, int_item, set_traits > set_type;

        set_type s( kSize, 3 );
        test( s );
    }

    struct set_static_traits: public cc::split_list::traits
    {
        static bool const dynamic_bucket_table = false;
    };

    TEST_F( SplitListIterableSet_DHP, static_bucket_table )
    {
        struct set_traits: public set_static_traits
        {
            typedef cc::iterable_list_tag ordered_list;
            typedef hash_int hash;
            typedef cds::atomicity::item_counter item_counter;

            struct ordered_list_traits: public cc::iterable_list::traits
            {
                typedef cmp compare;
                typedef cds::backoff::pause back_off;
            };
        };
        typedef cc::SplitListSet< gc_type, int_item, set_traits > set_type;

        set_type s( kSize, 4 );
        test( s );
    }

    TEST_F( SplitListIterableSet_DHP, static_bucket_table_free_list )
    {
        struct set_traits: public set_static_traits
        {
            typedef cc::iterable_list_tag ordered_list;
            typedef hash_int hash;
            typedef cds::atomicity::item_counter item_counter;
            typedef cds::intrusive::FreeList free_list;

            struct ordered_list_traits: public cc::iterable_list::traits
            {
                typedef cmp compare;
                typedef cds::backoff::pause back_off;
            };
        };
        typedef cc::SplitListSet< gc_type, int_item, set_traits > set_type;

        set_type s( kSize, 4 );
        test( s );
    }

} // namespace
