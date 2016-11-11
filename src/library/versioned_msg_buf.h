/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include "library/messages.h"
#include "util/name.h"

namespace lean {

class versioned_msg_buf : public message_buffer {
    // TODO(gabriel): structure as tree?
    struct msg_bucket {
        std::vector<message> m_msgs;
        period m_version = 0;

        std::unordered_set<name, name_hash> m_children;
    };

    mutex m_mutex;
    std::unordered_map<name, msg_bucket, name_hash> m_buf;

    void erase_bucket(name const & bucket);

public:
    versioned_msg_buf() {}

    void start_bucket(message_bucket_id const & bucket) override;
    void report(message_bucket_id const & bucket, message const & msg) override;
    void finish_bucket(message_bucket_id const & bucket, std::vector<name> const & children) override;

    std::vector<message> get_messages();
};

}
