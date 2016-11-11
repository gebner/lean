/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <utility>
#include <string>
#include <vector>
#include "library/versioned_msg_buf.h"

namespace lean {

void versioned_msg_buf::start_bucket(message_bucket_id const & bucket) {
    unique_lock<mutex> lock(m_mutex);

    if (!bucket.m_bucket.is_atomic()) {
        name parent = bucket.m_bucket.get_prefix();
        auto & parent_buf = m_buf[parent];
        if (parent_buf.m_version > bucket.m_version &&
                !parent_buf.m_children.count(bucket.m_bucket))
            return;
    }

    auto & buf = m_buf[bucket.m_bucket];
    if (buf.m_version < bucket.m_version) {
        buf.m_version = bucket.m_version;
        buf.m_msgs.clear();
    }
}

void versioned_msg_buf::report(message_bucket_id const & bucket, message const & msg) {
    unique_lock<mutex> lock(m_mutex);

    auto & buf = m_buf[bucket.m_bucket];
    if (buf.m_version < bucket.m_version) {
        throw exception("missing call to start_bucket");
    } else if (buf.m_version == bucket.m_version) {
        buf.m_msgs.push_back(msg);
    }
}

void versioned_msg_buf::finish_bucket(message_bucket_id const & bucket, std::vector<name> const & children) {
    unique_lock<mutex> lock(m_mutex);

    auto & buf = m_buf[bucket.m_bucket];
    if (buf.m_version != bucket.m_version) return;

    auto old_children = buf.m_children;
    buf.m_children.clear();

    for (auto & c : children)
        buf.m_children.insert(c);

    for (auto & c : old_children) {
        if (!buf.m_children.count(c)) {
            if (m_buf[c].m_version < bucket.m_version)
                erase_bucket(c);
        }
    }
}

std::vector<message> versioned_msg_buf::get_messages() {
    unique_lock<mutex> lock(m_mutex);
    std::vector<message> msgs;
    for (auto & buf : m_buf) {
        for (auto & msg : buf.second.m_msgs)
            msgs.push_back(msg);
    }
    return msgs;
}

void versioned_msg_buf::erase_bucket(name const & bucket) {
    for (auto c : m_buf[bucket].m_children) {
        erase_bucket(c);
    }
    m_buf.erase(bucket);
}

}
